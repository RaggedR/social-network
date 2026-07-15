-- | Type-safe API definition using Servant.
--
-- The API type IS the documentation. Change a type and every handler
-- that doesn't match fails to compile.
--
-- Six routes for the minimal social network:
--   POST   /users                 — create user (identity)
--   GET    /users/:handle         — get user profile
--   POST   /users/:uid/follow/:target  — follow (connection)
--   DELETE /users/:uid/follow/:target  — unfollow
--   POST   /users/:uid/posts     — create post (broadcast)
--   GET    /users/:uid/feed      — chronological feed
module SocialNetwork.Api
  ( API
  , api
  , CreateUserRequest (..)
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text)
import GHC.Generics (Generic)
import Servant

import SocialNetwork.Types (User, NewPost)
import SocialNetwork.Types qualified as T

-- | The complete API type.
--
-- In Servant, the type literally encodes every route, method,
-- request/response type, and URL parameter. This is checked at
-- compile time — a missing handler is a type error.
type API =
       -- Identity: create a user
       "users" :> ReqBody '[JSON] CreateUserRequest :> Post '[JSON] User
       -- Identity: get user by handle
  :<|> "users" :> Capture "handle" Text :> Get '[JSON] User
       -- Connection: follow someone
  :<|> "users" :> Capture "uid" Int :> "follow" :> Capture "target" Int :> PostNoContent
       -- Connection: unfollow
  :<|> "users" :> Capture "uid" Int :> "follow" :> Capture "target" Int :> DeleteNoContent
       -- Broadcast: create a post
  :<|> "users" :> Capture "uid" Int :> "posts" :> ReqBody '[JSON] NewPost :> Post '[JSON] T.Post
       -- Feed: chronological feed (the comonadic extract)
  :<|> "users" :> Capture "uid" Int :> "feed" :> Get '[JSON] [T.Post]

-- | Request for creating a user.
data CreateUserRequest = CreateUserRequest
  { reqHandle :: !Text
  , reqName   :: !Text
  }
  deriving stock (Generic, Show)

instance FromJSON CreateUserRequest
instance ToJSON CreateUserRequest

api :: Proxy API
api = Proxy
