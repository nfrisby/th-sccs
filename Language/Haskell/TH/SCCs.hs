module Language.Haskell.TH.SCCs
  (binding_group, binding_groups,
   scc, sccs,
   Dependencies(..), type_dependencies, td_recur, td_descend,
   Named(..),
   printQ
  ) where

import Language.Haskell.TH.Syntax

import qualified Data.Set as Set; import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Traversable as Traversable
import Control.Monad (liftM, liftM2, (<=<))

import Data.Graph (stronglyConnComp, SCC(..))


-- | Helpful for debugging generated code
printQ :: Show a => Maybe String -> Q a -> Q [Dec]
printQ s m = do
 x <- m
 runIO (maybe (return ()) putStr s >> print x) >> return []


-- | Computes the SCC that includes the declaration of the given name; @Left@
-- is a singly acyclic declaration, @Right@ is a mutually recursive group
-- (possibly of size one: singly recursion).
scc :: Name -> Q (Either Name (Set Name))
scc n = (head . filter (either (==n) (Set.member n))) `liftM` sccs [n]


-- | Computes all SCCs for the given names (including those it dominates)
sccs :: [Name] -> Q [Either Name (Set Name)]
sccs ns = do
  let withK f k = (,) k `liftM` f k
      chaotic f = loop <=< analyze where
        analyze = Traversable.mapM f . Map.fromList .
                  map (\ x -> (x, x)) . Set.toList
        loop m | Set.null fringe = return m
               | otherwise = Map.union m `liftM` analyze fringe >>= loop
          where fringe =
                  Set.unions (Map.elems m) `Set.difference` Map.keysSet m
  names <- chaotic (fmap type_dependencies . reify) (Set.fromList ns)
  let listify (AcyclicSCC v) = Left v
      listify (CyclicSCC vs) = Right (Set.fromList vs)
  return (map listify (stronglyConnComp [(n, n, Set.toList deps) |
                                         (n, deps) <- Map.assocs names]))

-- | Wrapper for 'scc' that forgets the distinction between a single acyclic
-- SCC and a singly recursive SCC
binding_group :: Name -> Q (Set Name)
binding_group = liftM binding_group' . scc

-- | Wrapper for 'sccs' that forgets the distinction between a single acyclic
-- SCC and a singly recursive SCC
binding_groups :: [Name] -> Q [Set Name]
binding_groups ns = (filter relevant . map binding_group') `liftM` sccs ns
  where relevant bg = not (Set.null (Set.intersection (Set.fromList ns) bg))

binding_group' = either Set.singleton id

-- | This is semantically murky: it's just the name of anything that
-- \"naturally\" /defines/ a name; error if it doesn't.
class Named t where name_of :: t -> Name

instance Named Info where
  name_of i = case i of
    ClassI d _ -> name_of d
    ClassOpI n _ _ _ -> n
    TyConI d -> name_of d
    PrimTyConI n _ _ -> n
    DataConI n _ _ _ -> n
    VarI n _ _ _ -> n
    TyVarI n _ -> n

instance Named Dec where
  name_of d = case d of
    FunD n _ -> n
    ValD p _ _ -> name_of p
    DataD _ n _ _ _ -> n
    NewtypeD _ n _ _ _ -> n
    TySynD n _ _ -> n
    ClassD _ n _ _ _ -> n
    FamilyD _ n _ _ -> n
    o -> error $ show o ++ " is not a named declaration."

instance Named Con where
  name_of c = case c of
    NormalC n _ -> n
    RecC n _ -> n
    InfixC _ n _ -> n
    ForallC _ _ c -> name_of c

instance Named Pat where
  name_of p = case p of
    VarP n -> n
    AsP n _ -> n
    SigP p _ -> name_of p
    o -> error $ "The pattern `" ++ show o ++ "' does not define exactly one name."



-- | Calculate the type declarations upon which this construct syntactically
-- depends. The first argument tracks the bindings traversed; use 'td_descend'
-- to maintain it.
class Dependencies t where
  type_dependencies' :: [Name] -> t -> Set Name

type_dependencies :: Dependencies t => t -> Set Name
type_dependencies = type_dependencies' []


-- | Just a bit shorter than 'type_dependencies''
td_recur :: Dependencies t => [Name] -> t -> Set Name
td_recur ns = type_dependencies' ns

-- | Shorter than 'type_dependencies'' and also adds the name of the seconda
-- argument to the tracked bindings
td_descend :: (Named a, Dependencies t) => [Name] -> a -> t -> Set Name
td_descend ns x = type_dependencies' (ns ++ [name_of x])

instance Dependencies Info where
  type_dependencies' ns i = case i of
    TyConI d -> td_descend ns i d
    PrimTyConI n _ _ -> Set.empty
    _ -> error $ "This version of th-sccs only calculates mutually " ++
                 "recursive groups for types; " ++ show (name_of i) ++
                 " is not a type."

instance Dependencies Dec where
  type_dependencies' ns d = case d of
    DataD _ _ _ cons _ -> Set.unions (map w cons)
    NewtypeD _ _ _ c _ -> w c
    TySynD _ _ ty -> w ty
    FamilyD {} ->
      error $ "This version of th-sccs cannot calculate mutually recursive " ++
              "groups for types involving type families; " ++
              show (last ns) ++ " uses " ++ show (name_of d) ++ "."
    o -> error $ "Unexpected declaration: " ++ show o ++ "."
    where w x = td_descend ns d x

instance Dependencies Con where
  type_dependencies' ns c = case c of
    NormalC _ sts -> w $ map snd sts
    RecC _ vsts -> w $ map (\ (n, _, t) -> RecordField n t) vsts
    InfixC stL _ stR -> w $ map snd [stL, stR]
    ForallC _ _ c -> type_dependencies' ns c
    where w xs = Set.unions (map (td_descend ns c) xs)

data RecordField = RecordField Name Type
instance Named RecordField where name_of (RecordField n _) = n
instance Dependencies RecordField where
  type_dependencies' ns rf@(RecordField _ ty) = td_descend ns rf ty

instance Dependencies Type where
  type_dependencies' ns t = case t of
    ForallT _ _ t -> w t
    ConT n -> Set.singleton n
    AppT tfn targ -> Set.union (w tfn) (w targ)
    SigT t _ -> w t
    _ -> Set.empty
    where w x = td_recur ns x
