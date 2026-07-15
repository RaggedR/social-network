-- | Domain types for the minimal social network.
--
-- These types serve double duty: they are the runtime data model AND the
-- template for Lean theorem statements. The algebraic structure here
-- mirrors the Lean definitions nearly 1:1.
module SocialNetwork.Types
  ( -- * Core identifiers
    UserId (..)
  , PostId (..)
    -- * Domain types
  , User (..)
  , Post (..)
  , NewPost (..)
  , Follow (..)
    -- * Social graph
  , SocialGraph (..)
  , emptyGraph
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Time (UTCTime)
import GHC.Generics (Generic)

-- | User identifier. Newtype for type safety — prevents mixing with PostId.
newtype UserId = UserId Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | Post identifier.
newtype PostId = PostId Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | A user profile.
data User = User
  { userId      :: !UserId
  , userHandle  :: !Text
  , displayName :: !Text
  , bio         :: !Text
  , userCreated :: !UTCTime
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON User
instance FromJSON User

-- | A post (broadcast), optionally with an audience restriction.
--
-- When @postAudience = Nothing@, all followers can see the post (sheaf).
-- When @postAudience = Just uids@, only those followers can see it (presheaf).
-- This is the exact point where the sheaf condition breaks.
data Post = Post
  { postId       :: !PostId
  , postAuthor   :: !UserId
  , postBody     :: !Text
  , postCreated  :: !UTCTime
  , postAudience :: !(Maybe [UserId])  -- Nothing = all followers (sheaf)
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON Post
instance FromJSON Post

-- | Request body for creating a new post.
-- When @newPostAudience@ is omitted or null, the post is visible to all followers.
-- When provided, only the listed user IDs can see it.
data NewPost = NewPost
  { newPostBody     :: !Text
  , newPostAudience :: !(Maybe [Int])  -- user IDs, or null for public
  }
  deriving stock (Eq, Show, Generic)

instance FromJSON NewPost

-- | A follow relationship (directed edge in the social graph).
data Follow = Follow
  { followerId  :: !UserId
  , followedId  :: !UserId
  , followCreated :: !UTCTime
  }
  deriving stock (Eq, Ord, Show, Generic)

instance ToJSON Follow

-- | The social graph: users + follow relation + a distinguished viewer.
--
-- This is the Shape type of our directed container.
-- In the Lean formalisation: @Shape := SocialGraph@
data SocialGraph = SocialGraph
  { graphUsers   :: !(Set UserId)
  , graphFollows :: !(Set (UserId, UserId))  -- (follower, followed)
  , graphViewer  :: !UserId
  }
  deriving stock (Eq, Show)

-- | The empty graph with a given viewer.
emptyGraph :: UserId -> SocialGraph
emptyGraph v = SocialGraph
  { graphUsers = Set.singleton v
  , graphFollows = Set.empty
  , graphViewer = v
  }
