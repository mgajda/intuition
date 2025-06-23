module Formulas where


import Data.TPTP
import Data.Text
import Data.Set
import qualified Data.Set as Set
import Data.Map
import qualified Data.Map as Map



{-| Computes the order of the given formula.
-}
get_order :: FirstOrder Unsorted -> Int

get_order (Connected phi1 Equivalence phi2) =
  let o1 = get_order phi1 in
    let o2 = get_order phi2 in
      1 + max o1 o2
get_order (Connected phi1 Implication phi2) = max (1+get_order phi1) (get_order phi2)
get_order (Connected phi1 ReversedImplication phi2) = max (1+get_order phi2) (get_order phi1)
get_order (Connected phi1 ExclusiveOr phi2) = max (get_order phi1) (get_order phi2)
get_order (Connected phi1 NegatedDisjunction phi2) = 1+max (get_order phi1) (get_order phi2)
get_order (Connected phi1 NegatedConjunction phi2) = 1+max (get_order phi1) (get_order phi2)
get_order (Connected phi1 Disjunction phi2) = max (get_order phi1) (get_order phi2)
get_order (Connected phi1 Conjunction phi2) = max (get_order phi1) (get_order phi2)
get_order (Negated phi1) = 1 + (get_order phi1)
get_order (Atomic (Predicate qq [])) = 0
get_order (Atomic (Predicate _ _)) = 0
get_order (Atomic (Equality _ _ _)) = 0
get_order (Quantified _ _ _) = 0 -- TODO: for first order formulas



{-| Computes the set of atoms that occur on positive positions in the given formula.
-}
positive_atoms_from_formula :: FirstOrder Unsorted -> Set Literal

positive_atoms_from_formula (Connected phi1 Equivalence phi2) = Set.empty
positive_atoms_from_formula (Connected phi1 Implication phi2) =
      let resphi1 = positive_atoms_from_formula phi2 in
      let resphi2 = negative_atoms_from_formula phi1 in
        Set.union resphi1 resphi2
positive_atoms_from_formula (Connected phi1 ReversedImplication phi2) = Set.empty
positive_atoms_from_formula (Connected phi1 ExclusiveOr phi2) = Set.empty
positive_atoms_from_formula (Connected phi1 NegatedDisjunction phi2) = Set.empty
positive_atoms_from_formula (Connected phi1 NegatedConjunction phi2) = Set.empty
positive_atoms_from_formula (Connected phi1 Disjunction phi2) = Set.empty
positive_atoms_from_formula (Connected phi1 Conjunction phi2) = Set.empty
positive_atoms_from_formula (Negated _) = Set.empty
positive_atoms_from_formula (Atomic (Predicate qq [])) = Set.singleton (Predicate qq [])
positive_atoms_from_formula (Atomic (Predicate _ _)) = Set.empty
positive_atoms_from_formula (Atomic (Equality _ _ _)) = Set.empty
positive_atoms_from_formula (Quantified _ _ _) = Set.empty



{-| Computes the set of atoms that occur on negative positions in the given formula.
-}
negative_atoms_from_formula :: FirstOrder Unsorted -> Set Literal
      
negative_atoms_from_formula (Connected phi1 Equivalence phi2) = Set.empty
negative_atoms_from_formula (Connected phi1 Implication phi2) =
      let resphi1 = negative_atoms_from_formula phi2 in
      let resphi2 = positive_atoms_from_formula phi1 in
        Set.union resphi1 resphi2
negative_atoms_from_formula (Connected phi1 ReversedImplication phi2) = Set.empty
negative_atoms_from_formula (Connected phi1 ExclusiveOr phi2) = Set.empty
negative_atoms_from_formula (Connected phi1 NegatedDisjunction phi2) = Set.empty
negative_atoms_from_formula (Connected phi1 NegatedConjunction phi2) = Set.empty
negative_atoms_from_formula (Connected phi1 Disjunction phi2) = Set.empty
negative_atoms_from_formula (Connected phi1 Conjunction phi2) = Set.empty
negative_atoms_from_formula (Negated _) = Set.empty
negative_atoms_from_formula (Atomic (Predicate qq [])) = Set.empty
negative_atoms_from_formula (Atomic (Predicate _ _)) = Set.empty
negative_atoms_from_formula (Atomic (Equality _ _ _)) = Set.empty
negative_atoms_from_formula (Quantified _ _ _) = Set.empty


{-| Result is true iff the given literal is not the target of the given
  formula.
-}
not_a_target :: FirstOrder Unsorted -> Literal -> Bool
      
not_a_target (Connected phi1 Equivalence phi2) _ = True
not_a_target (Connected phi1 Implication phi2) ltrl = not_a_target phi2 ltrl
not_a_target (Connected phi1 ReversedImplication phi2) _ = True
not_a_target (Connected phi1 ExclusiveOr phi2) _ = True
not_a_target (Connected phi1 NegatedDisjunction phi2) _ = True
not_a_target (Connected phi1 NegatedConjunction phi2) _ = True
not_a_target (Connected phi1 Disjunction phi2) _ = True
not_a_target (Connected phi1 Conjunction phi2) _ = True
not_a_target (Negated _) _ = True
not_a_target (Atomic (Predicate qq [])) ltrl =
      ltrl /= (Predicate qq [])
not_a_target (Atomic (Predicate qq xx)) _ = True
not_a_target (Atomic (Equality _ _ _)) _ = True
not_a_target (Quantified _ _ _) _ = True


remove_on_level :: FirstOrder Unsorted -> Literal -> Int -> Maybe (FirstOrder Unsorted)
remove_on_level phi ltrl n =
  if n>0 then
    case phi of
      Connected phi1 Implication phi2 ->
        let assmpt = (remove_on_level phi1 ltrl (n-1)) in
          case assmpt of
            Just phi1 -> case (remove_on_level phi2 ltrl n) of
                           Just phi2 -> Just (Connected phi1 Implication phi2)
                           Nothing -> Nothing
            Nothing -> remove_on_level phi2 ltrl n
      Connected _ _ _ -> Nothing
      Negated _ -> Nothing
      Atomic _ -> Nothing
      Quantified _ _ _ -> Nothing
  else
    case phi of
      Connected phi1 Implication phi2 ->
        let concl = (remove_on_level phi2 ltrl n) in
          case concl of
            Just phi2 -> Just (Connected phi1 Implication phi2)
            Nothing -> Nothing
      Connected _ _ _ -> Nothing
      Negated _ -> Nothing
      Atomic ltrl1 -> if ltrl == ltrl1
                      then Nothing
                      else Just phi
      Quantified _ _ _ -> Nothing

  

occurs_negatively :: FirstOrder Unsorted -> Literal -> Bool

occurs_negatively (Connected phi1 Equivalence phi2) _ = False
occurs_negatively (Connected phi1 Implication phi2) ltrl =
      (occurs_positively phi1 ltrl) && (occurs_negatively phi2 ltrl)
occurs_negatively (Connected phi1 ReversedImplication phi2) _ = False
occurs_negatively (Connected phi1 ExclusiveOr phi2) _ = False
occurs_negatively (Connected phi1 NegatedDisjunction phi2) _ = False
occurs_negatively (Connected phi1 NegatedConjunction phi2) _ = False
occurs_negatively (Connected phi1 Disjunction phi2) _ = False
occurs_negatively (Connected phi1 Conjunction phi2) _ = False
occurs_negatively (Negated _) _ = False
occurs_negatively (Atomic _) _ = False
occurs_negatively (Quantified _ _ _) _ = False



occurs_positively :: FirstOrder Unsorted -> Literal -> Bool

occurs_positively (Connected phi1 Equivalence phi2) _ = False
occurs_positively (Connected phi1 Implication phi2) ltrl =
      (occurs_negatively phi1 ltrl) && (occurs_positively phi2 ltrl)
occurs_positively (Connected phi1 ReversedImplication phi2) _ = False
occurs_positively (Connected phi1 ExclusiveOr phi2) _ = False
occurs_positively (Connected phi1 NegatedDisjunction phi2) _ = False
occurs_positively (Connected phi1 NegatedConjunction phi2) _ = False
occurs_positively (Connected phi1 Disjunction phi2) _ = False
occurs_positively (Connected phi1 Conjunction phi2) _ = False
occurs_positively (Negated _) _ = False
occurs_positively (Atomic (Predicate qq [])) (Predicate pp []) = pp == qq
occurs_positively (Atomic (Predicate qq [])) (Predicate _ _) = False
occurs_positively (Atomic (Predicate qq [])) (Equality _ _ _) = False
occurs_positively (Atomic _) _ = False
occurs_positively (Quantified _ _ _) _ = False



{-|
Gives the target literal of the given formula or Nothing if that does not exists.
-}
get_target :: FirstOrder Unsorted -> Maybe Literal

get_target (Connected phi1 Equivalence phi2) = Nothing
get_target (Connected phi1 Implication phi2) = get_target phi2
get_target (Connected phi1 ReversedImplication phi2) = Nothing
get_target (Connected phi1 ExclusiveOr phi2) = Nothing
get_target (Connected phi1 NegatedDisjunction phi2) = Nothing
get_target (Connected phi1 NegatedConjunction phi2) = Nothing
get_target (Connected phi1 Disjunction phi2) = Nothing
get_target (Connected phi1 Conjunction phi2) = Nothing
get_target (Negated phi1) = Nothing
get_target (Atomic (Predicate (Defined p) [])) = Just (Predicate (Defined p) [])
get_target (Atomic (Predicate (Reserved p) [])) = Just (Predicate (Reserved p) [])
get_target (Atomic (Predicate _ _)) = Nothing
get_target (Atomic (Equality _ _ _)) = Nothing
get_target (Quantified _ _ _) = Nothing



{-|
  We fix the name 'bot_c' to represent the falsity sentence.
-}
bot_c :: Name Predicate
bot_c = (Reserved . extended . pack)  "$bottom"



{-|
  The 'get_args' in case the given formula is an Implication or ReversedImplication returns the list of all assumptions of the implication.
-}
get_args :: FirstOrder Unsorted -> Set (FirstOrder Unsorted)
get_args v =
  case v of
    Connected phi1 Equivalence phi2 -> Set.empty
    Connected phi1 Implication phi2 -> Set.insert phi1 (get_args phi2)
    Connected phi1 ReversedImplication phi2 -> Set.insert phi2 (get_args phi1)
    Connected phi1 ExclusiveOr phi2 -> Set.empty
    Connected phi1 NegatedDisjunction phi2 -> Set.empty
    Connected phi1 NegatedConjunction phi2 -> Set.empty
    Connected phi1 Disjunction phi2 -> Set.empty
    Connected phi1 Conjunction phi2 -> Set.empty
    Negated _ -> Set.empty
    Atomic (Predicate pp []) -> Set.empty
    Atomic (Predicate _ _) -> Set.empty
    Atomic (Equality _ _ _) -> Set.empty
    Quantified _ _ _ -> Set.empty


  
args_tgt :: FirstOrder Unsorted -> (Set (FirstOrder Unsorted), Maybe Literal)

args_tgt frm = (get_args frm, get_target frm)



{-|
  The 'remove_atom_formula' removes occurrences of the given atom from the
  given formula. 
  The 'remove_atom_formula' does nontrivial work only when the first
  argument is atomic and the second argument is Implication.
-}
remove_atom_formula :: FirstOrder Unsorted -> FirstOrder Unsorted -> FirstOrder Unsorted

remove_atom_formula (Atomic (Predicate pp [])) (Connected phi1 Equivalence phi2) = (Connected phi1 Equivalence phi2)
remove_atom_formula (Atomic (Predicate pp [])) (Connected (Atomic (Predicate qq [])) Implication phi2) =
          let resphi2 = remove_atom_formula (Atomic (Predicate pp [])) phi2 in
            if pp == qq
            then resphi2
            else if resphi2 == Atomic (Predicate pp [])
                 then resphi2
                 else Connected (Atomic (Predicate qq [])) Implication resphi2
remove_atom_formula (Atomic (Predicate pp [])) (Connected phi1 Implication phi2) =
          let resphi1 = remove_atom_formula (Atomic (Predicate pp [])) phi1 in
          let resphi2 = remove_atom_formula (Atomic (Predicate pp [])) phi2 in
            if resphi1 == Atomic (Predicate pp [])
            then resphi2
            else if resphi2 == Atomic (Predicate pp [])
                 then resphi2
                 else Connected resphi1 Implication resphi2
remove_atom_formula (Atomic (Predicate pp [])) phi = phi
remove_atom_formula _ phi = phi



has_literal_on_level :: FirstOrder Unsorted -> Literal -> Int -> Bool
has_literal_on_level (Connected phi1 Implication phi2) ltrl n =
  if n>0
  then let inas = (has_literal_on_level phi1 ltrl (n-1)) in
         let inco = (has_literal_on_level phi2 ltrl n) in
           inas || inco
  else (has_literal_on_level phi2 ltrl n)
has_literal_on_level (Atomic ltrl1) ltrl n = (n <= 0) && ltrl == ltrl1
has_literal_on_level _ _ _ = False



remove_trivial_requirements :: FirstOrder Unsorted -> FirstOrder Unsorted

remove_trivial_requirements (Connected phi1 Implication phi2) = 
      case (remove_trivial_formula phi1) of
        Just phi1 -> Connected phi1 Implication (remove_trivial_requirements phi2)
        Nothing -> (remove_trivial_requirements phi2)
remove_trivial_requirements phi = phi



remove_trivial_formula :: FirstOrder Unsorted -> Maybe (FirstOrder Unsorted)

remove_trivial_formula phi =
  let target = get_target phi in
  let args = get_args phi in
    case target of
      Just tgt -> if (Prelude.foldl (\ sofar arg -> sofar || arg == (Atomic tgt)) False args)
                  then Nothing
                  else Just phi
      Nothing -> Just phi



{-| Compute the map from Literals to Ints.
    That gives the number of negative literals on levels greater than the
    second argument. We assume that the current formula is negative.
-}
get_map_for_deeper_neg_frm :: FirstOrder Unsorted -> Int -> Map Literal Int

get_map_for_deeper_neg_frm (Connected phi1 Equivalence phi2) _ = Map.empty
get_map_for_deeper_neg_frm (Connected phi1 Implication phi2) n =
  if (n>0)
  then unionWith (+) (get_map_for_deeper_pos_frm phi1 (n-1)) (get_map_for_deeper_neg_frm phi2 n)
  else get_map_for_deeper_neg_frm phi2 n
get_map_for_deeper_neg_frm (Connected phi1 ReversedImplication phi2) _ = Map.empty
get_map_for_deeper_neg_frm (Connected phi1 ExclusiveOr phi2) _ = Map.empty
get_map_for_deeper_neg_frm (Connected phi1 NegatedDisjunction phi2) _ = Map.empty
get_map_for_deeper_neg_frm (Connected phi1 NegatedConjunction phi2) _ = Map.empty
get_map_for_deeper_neg_frm (Connected phi1 Disjunction phi2) _ = Map.empty
get_map_for_deeper_neg_frm (Connected phi1 Conjunction phi2) _ = Map.empty
get_map_for_deeper_neg_frm (Negated phi1) _ = Map.empty
get_map_for_deeper_neg_frm (Atomic (Predicate (Defined p) [])) n =
  if (n>0)
  then Map.empty
  else Map.singleton (Predicate (Defined p) []) 1
get_map_for_deeper_neg_frm (Atomic (Predicate (Reserved p) [])) n =
  if (n>0)
  then Map.empty
  else Map.singleton (Predicate (Reserved p) []) 1
get_map_for_deeper_neg_frm (Atomic (Predicate _ _)) _ = Map.empty
get_map_for_deeper_neg_frm (Atomic (Equality _ _ _)) _ = Map.empty
get_map_for_deeper_neg_frm (Quantified _ _ _) _ = Map.empty


{-| Compute the map from Literals to Ints.
    That gives the number of negative literals on levels greater than the
    second argument. We assume that the current formula is positive.
-}
get_map_for_deeper_pos_frm :: FirstOrder Unsorted -> Int -> Map Literal Int

get_map_for_deeper_pos_frm (Connected phi1 Equivalence phi2) _ = Map.empty
get_map_for_deeper_pos_frm (Connected phi1 Implication phi2) n =
  if (n>0)
  then unionWith (+) (get_map_for_deeper_neg_frm phi1 (n-1)) (get_map_for_deeper_pos_frm phi2 n)
  else get_map_for_deeper_pos_frm phi2 n
get_map_for_deeper_pos_frm (Connected phi1 ReversedImplication phi2) _ = Map.empty
get_map_for_deeper_pos_frm (Connected phi1 ExclusiveOr phi2) _ = Map.empty
get_map_for_deeper_pos_frm (Connected phi1 NegatedDisjunction phi2) _ = Map.empty
get_map_for_deeper_pos_frm (Connected phi1 NegatedConjunction phi2) _ = Map.empty
get_map_for_deeper_pos_frm (Connected phi1 Disjunction phi2) _ = Map.empty
get_map_for_deeper_pos_frm (Connected phi1 Conjunction phi2) _ = Map.empty
get_map_for_deeper_pos_frm (Negated phi1) _ = Map.empty
get_map_for_deeper_pos_frm (Atomic (Predicate (Defined p) [])) _ = Map.empty
get_map_for_deeper_pos_frm (Atomic (Predicate (Reserved p) [])) n = Map.empty
get_map_for_deeper_pos_frm (Atomic (Predicate _ _)) _ = Map.empty
get_map_for_deeper_pos_frm (Atomic (Equality _ _ _)) _ = Map.empty
get_map_for_deeper_pos_frm (Quantified _ _ _) _ = Map.empty


{-| Compute the map from Literals to Ints. Given the argument
    phi = phi1 -> phi2 -> ... -> phik -> x
   it maps each literal p among phi1, phi2, ..., phik
   to the number of its occurrences in the sequence  phi1, phi2, ..., phik.
-}
get_map_for_leafs_frm_a :: FirstOrder Unsorted -> Map Literal Int

get_map_for_leafs_frm_a (Connected phi1 Equivalence phi2) = Map.empty
    -- Each leaflet contributes one.
get_map_for_leafs_frm_a (Connected (Atomic (Predicate (Defined p) [])) Implication phi2) =
      unionWith (+) (Map.singleton (Predicate (Defined p) []) 1) (get_map_for_leafs_frm_a phi2)
    -- Each leaflet contributes one.
get_map_for_leafs_frm_a (Connected (Atomic (Predicate (Reserved p) [])) Implication phi2) =
      unionWith (+) (Map.singleton (Predicate (Reserved p) []) 1) (get_map_for_leafs_frm_a phi2)
    -- Deeper argument formulas cannot contain leaflets.
get_map_for_leafs_frm_a (Connected _ Implication phi2) =
      get_map_for_leafs_frm_a phi2
get_map_for_leafs_frm_a (Connected phi1 ReversedImplication phi2) = Map.empty
get_map_for_leafs_frm_a (Connected phi1 ExclusiveOr phi2) = Map.empty
get_map_for_leafs_frm_a (Connected phi1 NegatedDisjunction phi2) = Map.empty
get_map_for_leafs_frm_a (Connected phi1 NegatedConjunction phi2) = Map.empty
get_map_for_leafs_frm_a (Connected phi1 Disjunction phi2) = Map.empty
get_map_for_leafs_frm_a (Connected phi1 Conjunction phi2) = Map.empty
get_map_for_leafs_frm_a (Negated phi1) = Map.empty
get_map_for_leafs_frm_a (Atomic (Predicate (Defined p) [])) = Map.empty
get_map_for_leafs_frm_a (Atomic (Predicate (Reserved p) [])) = Map.empty
get_map_for_leafs_frm_a (Atomic (Predicate _ _)) = Map.empty
get_map_for_leafs_frm_a (Atomic (Equality _ _ _)) = Map.empty
get_map_for_leafs_frm_a (Quantified _ _ _) = Map.empty



{-| Compute the set of Literals that occur negatively in the given formula,
    but as target of a subformula with arguments.
    We assume that the current formula is negative.
-}
get_negative_withargs_neg :: FirstOrder Unsorted -> Set Literal

get_negative_withargs_neg (Connected phi1 Equivalence phi2) = Set.empty
get_negative_withargs_neg (Connected phi1 Implication (Atomic (Predicate (Reserved p) []))) =
  Set.union (get_negative_withargs_pos phi1) (Set.singleton (Predicate (Reserved p) []))
get_negative_withargs_neg (Connected phi1 Implication phi2) =
  Set.union (get_negative_withargs_pos phi1) (get_negative_withargs_neg phi2)
get_negative_withargs_neg (Connected phi1 ReversedImplication phi2) = Set.empty
get_negative_withargs_neg (Connected phi1 ExclusiveOr phi2) = Set.empty
get_negative_withargs_neg (Connected phi1 NegatedDisjunction phi2) = Set.empty
get_negative_withargs_neg (Connected phi1 NegatedConjunction phi2) = Set.empty
get_negative_withargs_neg (Connected phi1 Disjunction phi2) = Set.empty
get_negative_withargs_neg (Connected phi1 Conjunction phi2) = Set.empty
get_negative_withargs_neg (Negated phi1) = Set.empty
get_negative_withargs_neg (Atomic (Predicate (Defined p) [])) = Set.empty
get_negative_withargs_neg (Atomic (Predicate (Reserved p) [])) = Set.empty
get_negative_withargs_neg (Atomic (Predicate _ _)) = Set.empty
get_negative_withargs_neg (Atomic (Equality _ _ _)) = Set.empty
get_negative_withargs_neg (Quantified _ _ _) = Set.empty


{-| Compute the set of Literals that occur negatively in the given formula,
    but as target of a subformula with arguments.
    We assume that the current formula is positive.
-}
get_negative_withargs_pos :: FirstOrder Unsorted -> Set Literal

get_negative_withargs_pos (Connected phi1 Equivalence phi2) = Set.empty
get_negative_withargs_pos (Connected phi1 Implication phi2) =
  Set.union (get_negative_withargs_neg phi1) (get_negative_withargs_pos phi2)
get_negative_withargs_pos (Connected phi1 ReversedImplication phi2) = Set.empty
get_negative_withargs_pos (Connected phi1 ExclusiveOr phi2) = Set.empty
get_negative_withargs_pos (Connected phi1 NegatedDisjunction phi2) = Set.empty
get_negative_withargs_pos (Connected phi1 NegatedConjunction phi2) = Set.empty
get_negative_withargs_pos (Connected phi1 Disjunction phi2) = Set.empty
get_negative_withargs_pos (Connected phi1 Conjunction phi2) = Set.empty
get_negative_withargs_pos (Negated phi1) = Set.empty
get_negative_withargs_pos (Atomic (Predicate (Defined p) [])) = Set.empty
get_negative_withargs_pos (Atomic (Predicate (Reserved p) [])) = Set.empty
get_negative_withargs_pos (Atomic (Predicate _ _)) = Set.empty
get_negative_withargs_pos (Atomic (Equality _ _ _)) = Set.empty
get_negative_withargs_pos (Quantified _ _ _) = Set.empty


{-| Compute the set of Literals that occur negatively in the given formula,
    but as target of a subformula with arguments.
    We assume that the current formula is negative.
-}
get_negative_noargs_neg :: FirstOrder Unsorted -> Set Literal

get_negative_noargs_neg (Connected phi1 Equivalence phi2) = Set.empty
get_negative_noargs_neg (Connected phi1 Implication (Atomic (Predicate (Reserved p) []))) =
 get_negative_noargs_pos phi1
get_negative_noargs_neg (Connected phi1 Implication phi2) =
  Set.union (get_negative_noargs_pos phi1) (get_negative_noargs_neg phi2)
get_negative_noargs_neg (Connected phi1 ReversedImplication phi2) = Set.empty
get_negative_noargs_neg (Connected phi1 ExclusiveOr phi2) = Set.empty
get_negative_noargs_neg (Connected phi1 NegatedDisjunction phi2) = Set.empty
get_negative_noargs_neg (Connected phi1 NegatedConjunction phi2) = Set.empty
get_negative_noargs_neg (Connected phi1 Disjunction phi2) = Set.empty
get_negative_noargs_neg (Connected phi1 Conjunction phi2) = Set.empty
get_negative_noargs_neg (Negated phi1) = Set.empty
get_negative_noargs_neg (Atomic (Predicate (Defined p) [])) = Set.empty
get_negative_noargs_neg (Atomic (Predicate (Reserved p) [])) = Set.empty
get_negative_noargs_neg (Atomic (Predicate _ _)) = Set.empty
get_negative_noargs_neg (Atomic (Equality _ _ _)) = Set.empty
get_negative_noargs_neg (Quantified _ _ _) = Set.empty


{-| Compute the set of Literals that occur negatively in the given formula,
    but as target of a subformula with arguments.
    We assume that the current formula is positive.
-}
get_negative_noargs_pos :: FirstOrder Unsorted -> Set Literal

get_negative_noargs_pos (Connected phi1 Equivalence phi2) = Set.empty
get_negative_noargs_pos (Connected phi1 Implication phi2) =
  Set.union (get_negative_noargs_neg phi1) (get_negative_noargs_pos phi2)
get_negative_noargs_pos (Connected phi1 ReversedImplication phi2) = Set.empty
get_negative_noargs_pos (Connected phi1 ExclusiveOr phi2) = Set.empty
get_negative_noargs_pos (Connected phi1 NegatedDisjunction phi2) = Set.empty
get_negative_noargs_pos (Connected phi1 NegatedConjunction phi2) = Set.empty
get_negative_noargs_pos (Connected phi1 Disjunction phi2) = Set.empty
get_negative_noargs_pos (Connected phi1 Conjunction phi2) = Set.empty
get_negative_noargs_pos (Negated phi1) = Set.empty
get_negative_noargs_pos (Atomic (Predicate (Defined p) [])) = Set.empty
get_negative_noargs_pos (Atomic (Predicate (Reserved p) [])) = Set.empty
get_negative_noargs_pos (Atomic (Predicate _ _)) = Set.empty
get_negative_noargs_pos (Atomic (Equality _ _ _)) = Set.empty
get_negative_noargs_pos (Quantified _ _ _) = Set.empty



{-| Creates formula by using the set of formulas as its arguments and
  the Literal as the target.
-}
combine_args_target :: Set (FirstOrder Unsorted) -> Literal -> FirstOrder Unsorted
combine_args_target args tgt =
  Data.Set.foldl (\ sofar frm -> Connected frm Implication sofar) (Atomic tgt) args


{-|
  Removes all but maybe one leaflets in requirements of the given formula provided that the target of the requirement
  is the given atom. The one leaflet that is not removed is the given atom.
-}
remove_leaflets_in_requirements_for_atom_of_formula :: FirstOrder Unsorted -> Literal -> (FirstOrder Unsorted, Map Literal Int)
remove_leaflets_in_requirements_for_atom_of_formula frm atom =
  let args = get_args frm in
    case get_target frm of
      Nothing -> (frm, Map.empty)
      Just tgt ->
        let (nargs, nmap) = Set.foldl (\ (accs, accm) arg ->
                                         case (get_target arg) of
                                           Nothing -> (Set.insert arg accs, accm)
                                           Just ntgt -> update_new_target ntgt arg accs accm)
                                      (Set.empty,Map.empty) args in
          (combine_args_target nargs tgt, nmap)
  where
    update_new_target ntgt argfrm accs accm =
      if ntgt /= atom
      then (Set.insert argfrm accs, accm)
      else let (narg, mrm) = remove_frmargs_with_exception argfrm atom in
             (Set.insert narg accs,
              Map.foldrWithKey (\ k wrm nmsofar ->
                                  Map.alter (\ mv -> case mv of
                                                       Nothing -> Just wrm
                                                       Just ov -> Just (ov+wrm)) k nmsofar) accm mrm)


{-|
  Returns a pair formula, map. 
  The resulting formula is constructed from the given one by removing all its arguments except from the given atom.
  The numbers of removed atoms are given in the returned map. Non-atomic arguments of the formula are deleted silently.
-}
remove_frmargs_with_exception :: FirstOrder Unsorted -> Literal -> (FirstOrder Unsorted, Map Literal Int)

remove_frmargs_with_exception (Connected (Atomic ltrl) Implication phi2) atom =
  let (frm, nmap) = (remove_frmargs_with_exception phi2 atom) in
      if ltrl == atom
        then 
        (Connected (Atomic ltrl) Implication frm, nmap)
        else (frm, Map.alter (\ v ->  case v of
                                        Nothing -> Just 1
                                        Just vv -> Just (vv+1)) ltrl nmap)
remove_frmargs_with_exception (Connected phi_1 Implication phi2) atom =
  remove_frmargs_with_exception phi2 atom
remove_frmargs_with_exception phi atom = (phi, Map.empty)

