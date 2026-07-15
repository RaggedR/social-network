-- | Servant server implementation wiring API routes to database operations.
module SocialNetwork.Server
  ( app
  , runServer
  ) where

import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import Network.Wai.Handler.Warp (run)
import Servant

import SocialNetwork.Api (API, api, CreateUserRequest (..))
import SocialNetwork.Db qualified as Db
import SocialNetwork.Types hiding (Post)
import SocialNetwork.Types qualified as T

-- | Build the WAI application.
app :: Db.Db -> Application
app conn = serve api (server conn)

-- | Run the server on a given port.
runServer :: Int -> Db.Db -> IO ()
runServer port conn = do
  putStrLn $ "Social network running on http://localhost:" <> show port
  run port (app conn)

-- | The server implementation: one handler per API route.
server :: Db.Db -> Server API
server conn =
       createUserH conn
  :<|> getUserH conn
  :<|> followH conn
  :<|> unfollowH conn
  :<|> createPostH conn
  :<|> getFeedH conn

-- Handlers

createUserH :: Db.Db -> CreateUserRequest -> Handler User
createUserH conn req =
  liftIO $ Db.createUser conn (reqHandle req) (reqName req)

getUserH :: Db.Db -> Text -> Handler User
getUserH conn handle' = do
  mUser <- liftIO $ Db.getUserByHandle conn handle'
  case mUser of
    Just u  -> pure u
    Nothing -> throwError err404

followH :: Db.Db -> Int -> Int -> Handler NoContent
followH conn uid target = do
  liftIO $ Db.follow conn (UserId uid) (UserId target)
  pure NoContent

unfollowH :: Db.Db -> Int -> Int -> Handler NoContent
unfollowH conn uid target = do
  liftIO $ Db.unfollow conn (UserId uid) (UserId target)
  pure NoContent

createPostH :: Db.Db -> Int -> NewPost -> Handler T.Post
createPostH conn uid req =
  liftIO $ Db.createPost conn (UserId uid) (newPostBody req) (newPostAudience req)

getFeedH :: Db.Db -> Int -> Handler [T.Post]
getFeedH conn uid =
  liftIO $ Db.getFeed conn (UserId uid)

