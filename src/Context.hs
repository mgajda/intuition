module Context where

import Data.List
import Data.TPTP
import Data.TPTP.Pretty
import Data.Text
import Data.TPTP.Parse.Text
import Data.Set
import qualified Data.Set as Set
import Data.Map 
import qualified Data.Map as Map
import Formulas


data AssumptionStatus_t =
  Fresh |
  Simplified |
  Used
     deriving (Eq,Ord)

instance Show AssumptionStatus_t where
  show Fresh = "Fresh"
  show Simplified = "Simplified"
  show Used = "Used"

data Assumption_t =
  Aspn (FirstOrder Unsorted) AssumptionStatus_t
     deriving (Ord)

  

instance Show Assumption_t where
  show (Aspn fof status) = "[[" ++ (show fof) ++ "--" ++ (show status) ++ "]]"

instance Eq Assumption_t where
   (Aspn fof1 _) == (Aspn fof2 _) = fof1 == fof2


to_formula :: Assumption_t -> FirstOrder Unsorted 
to_formula asmpt =
  case asmpt of
    Aspn frm _  -> frm




{-| Computes a map form Literals to Ints that given a Literal returns the
  number of its occurrences as target in formulas of the assumption set.
-}
compute_map_for_axiom_targets :: (Set Assumption_t) -> Map Literal Int
compute_map_for_axiom_targets axst =
    Set.foldl (\ mpsofar asmpt ->
                      let frm = to_formula asmpt in
                      let mtgt = get_target frm in
                        case mtgt of
                          Nothing -> mpsofar
                          Just tgt -> 
                            let hmany = Map.lookup tgt mpsofar in
                              case hmany of
                                Nothing -> Map.insert tgt 1 mpsofar
                                Just n -> Map.insert tgt (n+1) mpsofar) (Map.empty) axst
  

{-| Computes a map from Literals to Ints that given Literal returns the
  number of its occurrences on negative positions at levels deeper than 2.
-}
compute_map_for_deeper :: (Set Assumption_t) -> Map Literal Int
compute_map_for_deeper axst =
  Set.foldl (\ mpsofar asmpt ->
                     let frm = to_formula asmpt in
                     let mlfs = get_map_for_deeper_neg_frm frm 2 in
                       unionWith (+) mlfs mpsofar) (Map.empty) axst

frm_delete :: FirstOrder Unsorted -> Set Assumption_t -> Set Assumption_t
frm_delete formula assumptions =
  Set.filter (\ asm -> case asm of
                              Aspn frm _ -> frm /=formula ) assumptions

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

{-| The 'Context' type is a record with
   * the actual set of assumptions and
   * a map from negative literals in targets of axioms (second  argument)
     to the numbers of their occurrences as such and
   * a map from negative literals to the number of their negative occurrences
     on level deeper than 1
-}
data Context = Ctx  (Set Assumption_t) (Map Literal Int) (Map Literal Int)
  deriving (Eq, Show )

new_context :: Context
new_context = Ctx Set.empty Map.empty Map.empty

from_assumptions :: (Set Assumption_t) -> Context
from_assumptions assms =
  let tgts = compute_map_for_axiom_targets assms in
  let lfs = compute_map_for_deeper assms in
    Ctx assms tgts lfs

to_assumptions :: Context -> (Set Assumption_t)
to_assumptions ctx =
  case ctx of
    Ctx a _ _ -> a

to_deeper_negative :: Context -> (Set Literal)
to_deeper_negative ctx =
  case ctx of
    Ctx _ _ dn -> Map.keysSet dn

merge_contexts :: Context -> Context -> Context
merge_contexts ctx1 ctx2 =
  case ctx1 of
    Ctx frms1 lit1 lit2 ->
      case ctx2 of
        Ctx frms2 lit3 lit4 ->
          let nfrms = Set.union frms1 frms2 in
          let inter = Set.intersection frms1 frms2 in
          let minter  = compute_map_for_axiom_targets inter in
          let sum1 = unionWith (-) (unionWith (+) lit1 lit3) minter in
          let minter1 = compute_map_for_deeper inter in
          let sum2 = unionWith (-) (unionWith (+) lit2 lit4) minter1 in
            Ctx nfrms sum1 sum2


insert :: Assumption_t -> Context -> Context
insert asm ctx =
  case ctx of
    Ctx asms lit1 lit2 ->
      if Set.member asm asms
      then ctx
      else let nasms = Set.insert asm asms in
           let sgl = Set.singleton asm in
           let nlit1 = Map.unionWith (+) lit1 (compute_map_for_axiom_targets sgl) in
           let nlit2 = Map.unionWith (+) lit2 (compute_map_for_deeper sgl) in
             Ctx nasms nlit1 nlit2




mark_used :: Assumption_t -> Context -> Context
mark_used asm context =
  case context of
    Ctx asms lit1 lit2 ->
      case asm of
        Aspn phi _ ->
          let nasms = Set.map (\ frmc -> mark_one_used phi frmc) asms in
            Ctx nasms lit1 lit2

mark_one_used :: FirstOrder Unsorted -> Assumption_t -> Assumption_t
mark_one_used phi frmc =
  case frmc of
    Aspn phin Simplified -> if phi == phin
                            then  Aspn phi Used 
                            else frmc
    Aspn phin Fresh -> if phi == phin
                            then  Aspn phi Used 
                            else frmc
    Aspn phin _ -> frmc


get_formula_for_target :: Context -> Literal -> Maybe (FirstOrder Unsorted)
get_formula_for_target ctx tgt =
  case ctx of
    Ctx asmpts _ _ -> Set.foldl (\ el asm ->
                                        case el of
                                          Nothing ->
                                            let frm = to_formula asm in
                                              case get_target frm of
                                                Nothing -> Nothing
                                                Just ntgt ->
                                                  if ntgt == tgt
                                                  then Just frm
                                                  else Nothing
                                          Just e -> Just e) Nothing asmpts


{-|
  The 'positive_atoms' returns the set of literals that occur positively in
  given context.
-}
positive_atoms :: Context -> Set Literal
positive_atoms context =
  case context of
    Ctx frms lit1 lit2 ->
      Prelude.foldl (\ patm assmptn -> Set.union patm (positive_atoms_from_formula (to_formula assmptn))) Set.empty frms

{-|
  The 'negative_atoms' returns the set of literals that occur negatively in
  given context.
  TODO: this may be made more efficient by union of lit1 and lit2
-}
negative_atoms :: Context -> Set Literal
negative_atoms context =
  case context of
    Ctx frms lit1 lit2 ->
      Prelude.foldl (\ patm assmptn -> Set.union patm (negative_atoms_from_formula (to_formula assmptn))) Set.empty frms


{-|
  The 'remove_dead_assumptions' returns a context of assumptions obtained from 'assmpts' by
  removing ones with target 'literal' and removing literals from level 2.
-}
remove_dead_assumptions :: Context -> Literal -> Context
remove_dead_assumptions context literal =
  case context of
    Ctx frms lit1 lit2 ->
      let rmvwrotgt = Set.filter (\ asmpt -> case asmpt of
                                               Aspn phi _ -> not_a_target phi literal) frms in
      let resfrms = Set.map (\ asmpt -> case asmpt of
                                  Aspn phi x -> let rmv = (remove_on_level phi literal 2) in
                                                  case rmv of
                                                    Just nphi -> Aspn nphi x
                                                    Nothing -> Aspn phi x) rmvwrotgt in
        Ctx resfrms (Map.delete literal lit1) (Map.delete literal lit2)




{-|
  The 'is_atomic_in' checks if the given atomic formula is the same as in the given assumption.
-}
is_atomic_asm :: Name Predicate -> Assumption_t -> Bool
is_atomic_asm p asm =
  case asm of
    Aspn (Connected _ _ _) _ -> False
    Aspn (Negated _) _ -> False
    Aspn (Atomic (Predicate pp [])) _ -> p == pp
    Aspn (Atomic (Predicate pp (_ : _))) _ -> False
    Aspn (Atomic (Equality _ _ _)) _ -> False
    Aspn (Quantified _ _ _) _ -> False



{-|
  The 'is_atomic_in' checks if the given atomic formula is in the given set of assumptions.
-}
is_atomic_in :: Name Predicate -> Context -> Bool
is_atomic_in p context =
  case context of
    Ctx asms _ _ ->
      Set.foldl (\ sofar asm -> sofar || is_atomic_asm p asm) False asms


{-|
  The 'get_atoms' returns the set of atoms that are elements of the given context.
-}
get_atoms :: Context -> Set (FirstOrder Unsorted)
get_atoms context =
  case context of
    Ctx asms _ _ ->
      (Prelude.foldl (\ sofar assmptn ->
                         case assmptn of
                           Aspn (Connected _ _ _) _ -> sofar
                           Aspn (Negated _) _ -> sofar
                           Aspn (Atomic (Predicate pp [])) _ ->
                             Set.insert (Atomic (Predicate pp [])) sofar
                           Aspn (Atomic (Predicate pp (_ : _))) _ -> sofar
                           Aspn (Atomic (Equality _ _ _)) _ -> sofar
                           Aspn (Quantified _ _ _) _ -> sofar)
                       Set.empty asms)

{-|
  The 'remove_atom' removes occurrences of the given atom from the
  given assumption. 
-}
remove_atom :: FirstOrder Unsorted -> Assumption_t -> Assumption_t
remove_atom atm assmptn =
  case assmptn of
    Aspn phi feature -> Aspn (remove_atom_formula atm phi) feature

{-|
  The 'remove_atom_from_ctx' removes occurrences of the given atom 'atm' from
  all the assumptions in the given context.
-}
remove_atom_from_ctx :: FirstOrder Unsorted -> Context -> Context
remove_atom_from_ctx atm context =
  case context of
    Ctx assmpts _ _ ->
      let nassmpts = Set.foldl (\ sofar assmptn -> Set.insert (remove_atom atm assmptn) sofar) Set.empty  assmpts in
      from_assumptions nassmpts


{-|
  The 'remove_unfulfillable_assumptions_for_literals' returns a context obtained from 'context' by
  removing ones that contain negatively one of the given 'literals'.
-}
remove_unfulfillable_assumptions_for_literals :: Context -> Set Literal -> Context
remove_unfulfillable_assumptions_for_literals context literals =
  case context of
    Ctx assmpts _ _ ->
      let nassmpts = Set.foldl (\ sofar ltrl -> remove_unfulfillable_assumptions sofar ltrl) assmpts literals in
        from_assumptions nassmpts


{-|
  The 'remove_unfulfillable_assumptions' returns a set of assumptions obtained from 'assmpts' by
  removing ones with 'literal' on level 1.
-}
remove_unfulfillable_assumptions :: Set Assumption_t -> Literal -> Set Assumption_t
remove_unfulfillable_assumptions assmpts literal =
  Set.filter (\ asmpt -> case asmpt of
                               Aspn phi _ -> not (has_literal_on_level phi literal 1)) assmpts



{-|
  The 'goal_matches' checks if the second argument is the goal of the first argument.
-}
goal_matches :: Assumption_t -> Name Predicate -> Bool
goal_matches v p =
  (case v of
      Aspn (Connected phi1 Equivalence phi2) _ -> False
      Aspn (Connected phi1 Implication phi2) _ ->
           goal_matches (Aspn phi2 Fresh) p
      Aspn (Connected phi1 ReversedImplication phi2) _ ->
           goal_matches (Aspn phi1 Fresh) p
      Aspn (Connected phi1 ExclusiveOr phi2) _ -> False
      Aspn (Connected phi1 NegatedDisjunction phi2) _ -> False
      Aspn (Connected phi1 NegatedConjunction phi2) _ -> False
      Aspn (Connected phi1 Disjunction phi2) _ -> False
      Aspn (Connected phi1 Conjunction phi2) _ -> False
      Aspn (Negated _) _ -> False
      Aspn (Atomic (Predicate pp [])) _ -> p == pp
      Aspn (Atomic (Predicate _ _)) _ -> False
      Aspn (Atomic (Equality _ _ _)) _ -> False
      Aspn (Quantified _ _ _) _ -> False)


{-|
  The 'remove_dead_assumptions_for_literals' returns a list of assumptions obtained from ones in 'assmpts'
  by removing all ones that contain negatively 'literals'.
-}
remove_dead_assumptions_for_literals :: Context -> Set Literal -> Context
remove_dead_assumptions_for_literals assmpts literals =
  Set.foldl (\ sofar ltrl -> remove_dead_assumptions sofar ltrl) assmpts literals

{-
Get literals that are targets of axioms given number of times.
-}
get_literals_for_occurrences_atargets :: Context -> Int -> Set Literal
get_literals_for_occurrences_atargets (Ctx _ atgts _) nocc =
  Map.foldrWithKey ( \ ltr num acc -> if num == nocc
                                           then Set.insert ltr acc
                                           else acc) Set.empty atgts 

{-
   Get literals that occur at deeper negative positions and occur as such
   given number of times.
-}
get_literals_for_occurrences_deeper :: Context -> Int -> Set Literal
get_literals_for_occurrences_deeper (Ctx _ _ dtgts) nocc =
  Map.foldrWithKey ( \ ltr num acc -> if num == nocc
                                           then Set.insert ltr acc
                                           else acc) Set.empty dtgts



negative_only_as_noargs :: Context -> Set Literal
negative_only_as_noargs (Ctx assm atgts lfts) =
  let negative_withargs = Set.foldl (\ sofar as -> Set.union sofar (get_negative_withargs_neg (to_formula as))) Set.empty assm in
  let negative_noargs = Set.foldl (\ sofar as -> Set.union sofar (get_negative_noargs_neg (to_formula as))) Set.empty assm in
  Set.difference negative_noargs negative_withargs


remove_leaflets_in_requirements_of :: Context -> Set Literal -> Context
remove_leaflets_in_requirements_of context only_lfts=
  Set.foldl (\ ctx atom -> remove_leaflets_in_requirements_for_atom_of_context ctx atom) context only_lfts



remove_leaflets_in_requirements_for_atom_of_context :: Context -> Literal -> Context
remove_leaflets_in_requirements_for_atom_of_context (Ctx oassms atgts lfts) atom =
  let (nassms, nlfts) = Set.foldl acc_assumptions (Set.empty, lfts) oassms in
  let natgts = compute_map_for_axiom_targets nassms in
    Ctx nassms natgts nlfts
  where
    acc_assumptions (nnassms,lnlfts) (Aspn ofrm md) =
      (let (nfrm, removed) = remove_leaflets_in_requirements_for_atom_of_formula ofrm atom in
       let nnlfts = (Map.foldrWithKey (\ k rm nnnlfts ->
                                          Map.update (\ val ->
                                                         if val - rm > 0
                                                         then Just (val - rm)
                                                         else Nothing) k nnnlfts) lnlfts removed) in
         (Set.insert (Aspn nfrm md)  nnassms, nnlfts))


get_formulas_of_order :: Context -> Int -> Set (FirstOrder Unsorted)
get_formulas_of_order (Ctx assm _ _) ord =
  Set.foldl (\ sofar (Aspn frm _ ) -> if (get_order frm) == ord
                                      then Set.insert frm sofar
                                      else sofar) Set.empty assm
  
