-- | The social graph as a directed container comonad.
--
-- This module encodes the directed container operations from
-- Section 3 of social-network-ghani.tex. The five laws (D1–D5) are
-- proof obligations discharged in Lean, not runtime checks.
--
-- Lean correspondence:
--   root      ↔  DirectedContainer.root
--   egoNetwork ↔  DirectedContainer.sub
--   shift      ↔  DirectedContainer.shift
--   extract    ↔  DirectedContainer.counit
--   duplicate  ↔  DirectedContainer.comult
--   extend     ↔  DirectedContainer.extend
module SocialNetwork.Container
  ( -- * Extension functor
    Ext (..)
    -- * Directed container operations
  , root
  , egoNetwork
  , shift
    -- * Comonad operations
  , extract
  , duplicate
  , extend
    -- * Feed construction
  , chronologicalFeed
  ) where

import Data.Set qualified as Set
import Data.Ord (Down (..))
import Data.List (sortOn)
import SocialNetwork.Types

-- | The extension functor: a shape (social graph) paired with a
-- labelling of positions (users) by values.
--
-- Lean: @Ext C X = (s : C.Shape) × (C.Pos s → X)@
data Ext x = Ext !SocialGraph (UserId -> x)

instance Functor Ext where
  fmap f (Ext g v) = Ext g (f . v)

-- | Root: the logged-in viewer's position.
--
-- Lean: @root := fun g => g.viewer@
-- Law D1 depends on this: ego(g, root(g)) = g
root :: SocialGraph -> UserId
root = graphViewer

-- | Ego network: the subgraph visible from a given user's perspective.
-- Contains the user themselves plus everyone they follow.
--
-- Lean: @sub := fun g u => egoNetwork g u@
-- This is the key operation — it defines "what user u can see."
egoNetwork :: SocialGraph -> UserId -> SocialGraph
egoNetwork g u =
  let followed = Set.fromList
        [ b | (a, b) <- Set.toList (graphFollows g), a == u ]
      visibleUsers = Set.insert u followed
      visibleFollows = Set.filter
        (\(a, _) -> a == u)
        (graphFollows g)
  in SocialGraph
    { graphUsers = visibleUsers
    , graphFollows = visibleFollows
    , graphViewer = u
    }

-- | Shift: navigate from position p to position q within p's ego network.
-- Since positions are users and ego networks are subgraphs, this is
-- simply the identity on users (inclusion).
--
-- Lean: @shift := fun g _ q => q@
-- D5 (associativity) is trivial because shift is inclusion.
shift :: SocialGraph -> UserId -> UserId -> UserId
shift _ _ q = q

-- | Comonadic extract: get the value at the root position.
--
-- For a social network: "my own content."
-- Lean: @counit ⟨s, v⟩ = v (root s)@
extract :: Ext x -> x
extract (Ext g v) = v (root g)

-- | Comonadic duplicate: replace each position with its local view.
--
-- For a social network: "feed of feeds" — at each position p, you get
-- the entire Ext from p's perspective (p's ego network with the
-- labelling restricted to p's visible users).
--
-- Lean: @comult ⟨s, v⟩ = ⟨s, λp. ⟨s ↓ p, λq. v(p ⊕ q)⟩⟩@
duplicate :: Ext x -> Ext (Ext x)
duplicate (Ext g v) = Ext g $ \p ->
  Ext (egoNetwork g p) $ \q ->
    v (shift g p q)

-- | Comonadic extend: apply a local operation at every position.
--
-- This is THE feed algorithm combinator. Given a function that
-- inspects a local neighbourhood and produces a summary, extend
-- applies it at every position in the graph.
--
-- Lean: @extend f ⟨s, v⟩ = ⟨s, λp. f ⟨s ↓ p, λq. v(p ⊕ q)⟩⟩@
extend :: (Ext x -> y) -> Ext x -> Ext y
extend f (Ext g v) = Ext g $ \p ->
  f $ Ext (egoNetwork g p) $ \q ->
    v (shift g p q)

-- | A concrete feed algorithm: reverse-chronological feed.
--
-- This is a coKleisli morphism: Ext [Post] → [Post]
-- It inspects the local neighbourhood (posts from people the viewer
-- follows) and returns them sorted newest-first.
chronologicalFeed :: Ext [Post] -> [Post]
chronologicalFeed (Ext g postsFor) =
  let followed = [ b | (a, b) <- Set.toList (graphFollows g), a == root g ]
      allPosts = concatMap postsFor (root g : followed)
  in sortOn (Down . postCreated) allPosts
