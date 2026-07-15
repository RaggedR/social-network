-- | SQLite database layer for the social network.
--
-- Four tables:
--   users(id, handle, display_name, bio, created_at)
--   follows(follower_id, followed_id, created_at)
--   posts(id, author_id, body, created_at)
--   post_audience(post_id, user_id)  — the sheaf-breaking table
module SocialNetwork.Db
  ( Db
  , withDb
  , initDb
    -- * Users
  , createUser
  , getUser
  , getUserByHandle
    -- * Follows
  , follow
  , unfollow
  , getFollowing
  , getFollowers
    -- * Posts
  , createPost
  , getFeed
  , getUserPosts
  ) where

import Control.Monad (forM_)
import Data.Text (Text)
import Data.Time (UTCTime, getCurrentTime)
import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow ()
import SocialNetwork.Types

type Db = Connection

withDb :: FilePath -> (Db -> IO a) -> IO a
withDb path = withConnection path

initDb :: Db -> IO ()
initDb conn = do
  execute_ conn
    "CREATE TABLE IF NOT EXISTS users (\
    \  id INTEGER PRIMARY KEY AUTOINCREMENT,\
    \  handle TEXT NOT NULL UNIQUE,\
    \  display_name TEXT NOT NULL,\
    \  bio TEXT NOT NULL DEFAULT '',\
    \  created_at TEXT NOT NULL\
    \)"
  execute_ conn
    "CREATE TABLE IF NOT EXISTS follows (\
    \  follower_id INTEGER NOT NULL,\
    \  followed_id INTEGER NOT NULL,\
    \  created_at TEXT NOT NULL,\
    \  PRIMARY KEY (follower_id, followed_id),\
    \  FOREIGN KEY (follower_id) REFERENCES users(id),\
    \  FOREIGN KEY (followed_id) REFERENCES users(id)\
    \)"
  execute_ conn
    "CREATE TABLE IF NOT EXISTS posts (\
    \  id INTEGER PRIMARY KEY AUTOINCREMENT,\
    \  author_id INTEGER NOT NULL,\
    \  body TEXT NOT NULL,\
    \  created_at TEXT NOT NULL,\
    \  FOREIGN KEY (author_id) REFERENCES users(id)\
    \)"
  -- The sheaf-breaking table: per-post audience restriction.
  -- When a post has rows here, only listed users can see it.
  -- When a post has NO rows here, all followers can see it (sheaf case).
  execute_ conn
    "CREATE TABLE IF NOT EXISTS post_audience (\
    \  post_id INTEGER NOT NULL,\
    \  user_id INTEGER NOT NULL,\
    \  PRIMARY KEY (post_id, user_id),\
    \  FOREIGN KEY (post_id) REFERENCES posts(id),\
    \  FOREIGN KEY (user_id) REFERENCES users(id)\
    \)"
  -- Indices for the feed query
  execute_ conn
    "CREATE INDEX IF NOT EXISTS idx_posts_author ON posts(author_id)"
  execute_ conn
    "CREATE INDEX IF NOT EXISTS idx_follows_follower ON follows(follower_id)"
  execute_ conn
    "CREATE INDEX IF NOT EXISTS idx_post_audience_post ON post_audience(post_id)"

-- Users

createUser :: Db -> Text -> Text -> IO User
createUser conn handle' name = do
  now <- getCurrentTime
  execute conn
    "INSERT INTO users (handle, display_name, bio, created_at) VALUES (?, ?, '', ?)"
    (handle', name, show now)
  rowId <- lastInsertRowId conn
  pure User
    { userId = UserId (fromIntegral rowId)
    , userHandle = handle'
    , displayName = name
    , bio = ""
    , userCreated = now
    }

getUser :: Db -> UserId -> IO (Maybe User)
getUser conn (UserId uid) = do
  rows <- query conn
    "SELECT id, handle, display_name, bio, created_at FROM users WHERE id = ?"
    (Only uid)
  pure $ case rows of
    [(i, h, n, b, t)] -> Just (mkUser i h n b t)
    _ -> Nothing

getUserByHandle :: Db -> Text -> IO (Maybe User)
getUserByHandle conn handle' = do
  rows <- query conn
    "SELECT id, handle, display_name, bio, created_at FROM users WHERE handle = ?"
    (Only handle')
  pure $ case rows of
    [(i, h, n, b, t)] -> Just (mkUser i h n b t)
    _ -> Nothing

mkUser :: Int -> Text -> Text -> Text -> String -> User
mkUser i h n b t = User
  { userId = UserId i
  , userHandle = h
  , displayName = n
  , bio = b
  , userCreated = read t
  }

-- Follows

follow :: Db -> UserId -> UserId -> IO ()
follow conn (UserId a) (UserId b) = do
  now <- getCurrentTime
  execute conn
    "INSERT OR IGNORE INTO follows (follower_id, followed_id, created_at) VALUES (?, ?, ?)"
    (a, b, show now)

unfollow :: Db -> UserId -> UserId -> IO ()
unfollow conn (UserId a) (UserId b) =
  execute conn
    "DELETE FROM follows WHERE follower_id = ? AND followed_id = ?"
    (a, b)

getFollowing :: Db -> UserId -> IO [UserId]
getFollowing conn (UserId uid) = do
  rows <- query conn
    "SELECT followed_id FROM follows WHERE follower_id = ?"
    (Only uid) :: IO [Only Int]
  pure [UserId i | Only i <- rows]

getFollowers :: Db -> UserId -> IO [UserId]
getFollowers conn (UserId uid) = do
  rows <- query conn
    "SELECT follower_id FROM follows WHERE followed_id = ?"
    (Only uid) :: IO [Only Int]
  pure [UserId i | Only i <- rows]

-- Posts

-- | Create a post with optional audience restriction.
-- When audience is Nothing, all followers can see it (sheaf).
-- When audience is Just uids, only those users can see it (presheaf).
createPost :: Db -> UserId -> Text -> Maybe [Int] -> IO Post
createPost conn (UserId uid) body' mAudience = do
  now <- getCurrentTime
  execute conn
    "INSERT INTO posts (author_id, body, created_at) VALUES (?, ?, ?)"
    (uid, body', show now)
  rowId <- lastInsertRowId conn
  let pid = fromIntegral rowId :: Int
  -- Insert audience restrictions if provided.
  -- Always include the author in the audience (author can see own posts).
  forM_ mAudience $ \audienceIds -> do
    let allIds = if uid `elem` audienceIds then audienceIds else uid : audienceIds
    forM_ allIds $ \targetUid ->
      execute conn
        "INSERT OR IGNORE INTO post_audience (post_id, user_id) VALUES (?, ?)"
        (pid, targetUid)
  -- Read back the audience for the response
  audience <- getPostAudience conn pid
  pure Post
    { postId = PostId pid
    , postAuthor = UserId uid
    , postBody = body'
    , postCreated = now
    , postAudience = audience
    }

getPostAudience :: Db -> Int -> IO (Maybe [UserId])
getPostAudience conn pid = do
  rows <- query conn
    "SELECT user_id FROM post_audience WHERE post_id = ?"
    (Only pid) :: IO [Only Int]
  pure $ case rows of
    [] -> Nothing  -- no audience restriction
    _  -> Just [UserId i | Only i <- rows]

-- | The feed query, now with audience filtering.
--
-- A post is visible to viewer :me if:
--   1. The viewer follows the author (or is the author), AND
--   2. Either the post has no audience restriction (no rows in post_audience),
--      OR the viewer is in the audience.
--
-- Condition 2 is the sheaf-breaking filter. Without it, we have a sheaf.
getFeed :: Db -> UserId -> IO [Post]
getFeed conn (UserId uid) = do
  rows <- query conn
    "SELECT DISTINCT p.id, p.author_id, p.body, p.created_at FROM posts p \
    \LEFT JOIN follows f ON p.author_id = f.followed_id AND f.follower_id = ? \
    \WHERE (p.author_id = ? OR f.follower_id IS NOT NULL) \
    \  AND (NOT EXISTS (SELECT 1 FROM post_audience pa WHERE pa.post_id = p.id) \
    \       OR EXISTS (SELECT 1 FROM post_audience pa WHERE pa.post_id = p.id AND pa.user_id = ?)) \
    \ORDER BY p.created_at DESC \
    \LIMIT 50"
    (uid, uid, uid)
  -- Enrich each post with its audience
  mapM enrichWithAudience rows
  where
    enrichWithAudience (i, a, b, t) = do
      audience <- getPostAudience conn i
      pure (mkPost i a b t) { postAudience = audience }

getUserPosts :: Db -> UserId -> IO [Post]
getUserPosts conn (UserId uid) = do
  rows <- query conn
    "SELECT id, author_id, body, created_at FROM posts \
    \WHERE author_id = ? ORDER BY created_at DESC LIMIT 50"
    (Only uid)
  pure [mkPost i a b t | (i, a, b, t) <- rows]

mkPost :: Int -> Int -> Text -> String -> Post
mkPost i a b t = Post
  { postId = PostId i
  , postAuthor = UserId a
  , postBody = b
  , postCreated = read t
  , postAudience = Nothing  -- populated by enrichWithAudience
  }
