module Prover where

import Data.List
import Data.TPTP
import Data.TPTP.Pretty
import Data.Text
import Data.TPTP.Parse.Text
import Data.Set
import qualified Data.Set as Set
import Context
import Formulas

data Measure_t =
   MInt Int | MError String deriving (Show, Eq)


measure_allows :: Measure_t -> Bool
measure_allows measure =
  case measure of
   MInt n -> n>0
   MError _ -> False


combine_res :: a -> a -> a
combine_res x y = y

newmeasure :: Measure_t -> Assumption_t -> Name Predicate -> Measure_t
newmeasure (MInt n) phi goal = MInt (n - 1)
newmeasure (MError s) phi goal = MError s

proverres :: Context -> FirstOrder Unsorted -> Measure_t -> String
proverres assum goal measure =
  let res = prover assum goal measure in
    case res of
      Nothing -> "Fail"
      Just (MError s) -> "Fail: " ++ s
      Just (MInt n) -> "OK"



{-|
  The 'simplify1' simplifies formulas in context by finding all atoms that are assumed there
  except from the current goal and removing them from all the formulas.
-}
-- 1. Jeśli jest aksjomat atomowy a- to można wyrzucić wszystkie żądania 2.
simplify1  :: Context -> Literal -> Context
simplify1 context pred = 
  let atms = Set.filter (\atm ->  case atm of
                                        Atomic ltrl -> ltrl /= pred
                                        _ -> False)
             (get_atoms context)
  in Set.foldl (\ sofarctx atm -> remove_atom_from_ctx atm sofarctx)
               context atms

-- 2. Jeśli umiemy udowodnić jakiś atom to możn dodać go jako aksjomat
--     (ze skutkiem jak 1).
-- alx: tu bym sobie uprościł: jeśli umiemy udowodnić atom korzystając
--      wyłącznie z założeń pierwszego rzędu
simplify2  :: Context -> Context
simplify2 context =
  let o1 = get_formulas_of_order context 1 in
  let o0 = get_formulas_of_order context 0 in
  let no0 = iterate_reach o1 (o0, True) in
  let asms0 = Set.map (\ frm -> Aspn frm Fresh) no0 in 
    merge_contexts context (from_assumptions asms0)

iterate_reach :: Set (FirstOrder Unsorted) -> (Set (FirstOrder Unsorted), Bool) -> Set (FirstOrder Unsorted)
iterate_reach o1 (reach, False) = reach
iterate_reach o1 (reach, True) =
  iterate_reach o1
                (Set.foldl (\ (nreach, chg) nfrm ->
                               if target_reachable nfrm nreach
                               then case (get_target nfrm) of
                                      Nothing -> (nreach,chg)
                                      Just tgt -> if Set.member (Atomic tgt) nreach
                                                  then (nreach,chg)
                                                  else (Set.insert (Atomic tgt) nreach, True)
                               else (nreach, chg)) (reach, False) o1)
  where
    target_reachable nfrm reach =
      let args = get_args nfrm in
        Set.null (Set.difference args reach)

  

-- 3. Zbędne założenie: jeśli nigdzie nie ma c+ to można usunąć aksjomaty
--     i listki c-.
-- weźmy te atomy, które występują na pozycjach negatywnych, odejmijmy te, które są pozytywne
simplify3  :: Context -> Literal -> Context
simplify3 context goal =
  let pa = positive_atoms context in 
  let na = negative_atoms context in -- c+ occur negatively in formulas of the context
  let nowherecplus = Data.Set.delete goal (Data.Set.difference pa na) in
    remove_dead_assumptions_for_literals context nowherecplus





-- 4. Brak założenia: jeśli nigdzie nie ma c- to można usunąć aksjomaty,
--     w których są żądania c+
simplify4  :: Context -> Context
simplify4 context = 
  let pa = positive_atoms context in 
  let na = negative_atoms context in -- c+ occur negatively in formulas of the context
  let nowherecminus = (Data.Set.difference na pa) in
    remove_unfulfillable_assumptions_for_literals context nowherecminus

-- 5. Trywialne żądanie: można usunąć żądanie c+ z listkiem c+ (taka
--     sytuacja może być wynikiem wcześniejszego działania.
simplify5  :: Context -> Context
simplify5 (Ctx asmpts _ _) =
      let nasmpts = Set.foldl (\ sofar assmpt ->
                                 case assmpt of
                                   Aspn phi x -> Set.insert (Aspn (remove_trivial_requirements phi) x) sofar) Set.empty asmpts in
        from_assumptions nasmpts




-- 6. Tylko jedno wystąpienie negatywne a- jako cel aksjomatu: jak na
--     rysunku w pliku notatka1. Można to zrobić pod warunkiem, że a+
--     nie jest celem głównym. Jeśli jest, to też można coś zrobić.
simplify6  :: Context -> Literal -> Context
simplify6 context goal =
  let os_atargets = get_literals_for_occurrences_atargets context 1 in
     -- os_atargets - set of literals that are targets of axioms only once
  let os_deep_negative = to_deeper_negative context in
     -- os_dead_negative - set of literals that occur at negative positions deeper than 2
  let one_shot_negative_atargets = Data.Set.delete goal (Data.Set.difference os_atargets os_deep_negative) in
    Data.Set.foldl (\ ctx tgt -> transform_with_unique_axiom_target ctx tgt) context one_shot_negative_atargets

transform_with_unique_axiom_target :: Context -> Literal -> Context
transform_with_unique_axiom_target ctx tgt =
  let muformula = get_formula_for_target ctx tgt in -- get the only assumption with the target tgt
    case muformula of
      Nothing -> ctx
      Just uformula ->
        let args = get_args uformula in -- its arguments will be substituted for tgt in other assumptions
        let prepargs = Data.Set.foldl (\ st arg -> Data.Set.insert (args_tgt arg) st) Data.Set.empty args in
          -- prepargs are args presented as pairs (set of assumptions, target)
        let assmps = frm_delete uformula (to_assumptions ctx) in
          -- assmps is the context flattened to a set of assumptions, moreover uformula is removed
        let nassmpts = Data.Set.foldl (\ st asm -> Data.Set.insert (transform_preparg tgt asm prepargs) st)
                                      Data.Set.empty assmps in
          -- nassmpts are all assumptions with requests for atom tgt are replaced according to the rule
          from_assumptions nassmpts

{-| Change frm by replacing requests of the target tgt in this formula with
prepargs augmented by argumets of the requests.
-}
transform_preparg :: Literal -> Assumption_t -> Set (Set (FirstOrder Unsorted), Maybe Literal) -> Assumption_t
transform_preparg tgt (Aspn frm md) prepargs =
  let args = get_args frm in
    case get_target frm of
      Nothing -> (Aspn frm md)
      Just frmtgt -> 
        let nwargs = Data.Set.foldl (\ aset arg ->
                                        case get_target arg of
                                          Nothing -> Data.Set.insert arg aset
                                          Just atgt -> if atgt == tgt
                                                       then Data.Set.union (combine_formulas_from_prepargs (get_args arg) prepargs) aset
                                                       else Data.Set.insert arg aset)
                                    Data.Set.empty
                                    args in
        (Aspn (combine_args_target nwargs frmtgt) md)

{-| The procedure takes the set 'uargs' of FirstOrder formulas in the
  first argument, these are new arguments, and a set of pairs
  'prepargs' that represent the goal and the arguments of a
  formula. As a result it creates a set of FirstOrder Unsorted
  formulas by adding the new arguments to the arguments sets in
  'prepargs' and turning all pairs (new argument set, target) into
  respective formulas.
-}
combine_formulas_from_prepargs :: (Set (FirstOrder Unsorted)) ->
                                  (Set (Set (FirstOrder Unsorted), Maybe Literal)) -> Set (FirstOrder Unsorted)
combine_formulas_from_prepargs uargs prepargs =
  Data.Set.foldl (\ aset (aags, mtgt) ->
                     case mtgt of
                       Nothing -> aset
                       Just tgt -> Data.Set.insert (combine_args_target (Data.Set.union uargs aags) tgt) aset)
                 Data.Set.empty
                 prepargs
                                    

-- 7. Wszystkie wystąpienia negatywne a- są listkami: można uciąć
--     wszystkie listki w żądaniach o celu a+
simplify7  :: Context -> Context
simplify7 context =
  let only_lfts = negative_only_as_noargs context in
    remove_leaflets_in_requirements_of context only_lfts

simplify_dpll :: Context -> Literal -> Context
simplify_dpll context pred =
  -- 1. Jeśli jest aksjomat atomowy a- to można wyrzucić wszystkie żądania 2.
  let context1 =
        simplify1 context pred in
  -- 2. Jeśli umiemy udowodnić jakiś atom to możn dodać go jako aksjomat
  --     (ze skutkiem jak 1).
  let context2 = simplify2 context1 in
  -- 3. Zbędne założenie: jeśli nigdzie nie ma c+ to można usunąć aksjomaty
  --     i listki c-.
  let context3 = simplify3 context2 pred in
  -- 4. Brak założenia: jeśli nigdzie nie ma c- to można usunąć aksjomaty,
  --     w których są żądania c+
  let context4 = simplify4 context3 in
  -- 5. Trywialne żądanie: można usunąć żądanie c+ z listkiem c+ (taka
  --     sytuacja może być wynikiem wcześniejszego działania.
  let context5 =
        simplify5 context4 in
  -- 6. Tylko jedno wystąpienie negatywne a- jako cel aksjomatu: jak na
  --     rysunku w pliku notatka1. Można to zrobić pod warunkiem, że a+
  --     nie jest celem głównym. Jeśli jest, to też można coś zrobić.
  let context6 =
        simplify6 context5 pred in
  -- 7. Wszystkie wystąpienia negatywne a- są listkami: można uciąć
  --     wszystkie listki w żądaniach o celu a+
  simplify7 context6 



prover :: Context -> FirstOrder Unsorted -> Measure_t -> Maybe Measure_t
prover context (Connected  phi1 Equivalence phi2) measure =
  Just (MError "Unhandled equivalence in goal")
prover context (Connected phi1 Implication phi2) measure =
  prover (Context.insert (Aspn phi1 Fresh) context) phi2 measure
prover context (Connected phi1 ReversedImplication phi2) measure =
  Just (MError "Unhandled reversed implication in goal")
prover context (Connected phi1 ExclusiveOr phi2) measure =
  Just (MError "Unhandled connective XOR in goal")
prover context (Connected phi1 NegatedDisjunction phi2) measure =
  Just (MError "Unhandled connective NOR in goal")
prover context (Connected phi1 NegatedConjunction phi2) measure =
  Just (MError "Unhandled connective NAND in goal")
prover context (Connected phi1 Disjunction phi2) measure =
  Just (MError "Unhandled disjunction in goal")
prover context (Connected phi1 Conjunction phi2) measure =
  Just (MError "Unhandled conjunction in goal")
prover context (Negated phi) measure =
  Just (MError "Unhandled negation in goal")
prover context (Atomic (Predicate p [])) measure =
      let ncontext = simplify_dpll context (Predicate p []) in
      if (is_atomic_in p context)
      then Just measure
      else if (measure_allows measure)
           then try_context_assumptions context p measure 
           else (case measure of
                   MInt _ ->
                     Just (MError ("Measure exceeded at an attempt to prove " ++
                                   (Set.foldl (\ str el -> str ++ ", " ++ (show el)) "" (to_assumptions context)) ++
                                   " |- " ++ (show p)))
                   MError s -> Just (MError s))
prover context (Atomic (Predicate _ (_:_))) measure = Just (MError "Unhandled atomic proposition form")
prover context (Atomic (Equality _ _ _)) measure = Just (MError "Unhandled equality")
prover context (Quantified _ _ _) measure = Just (MError "Unhandled quantification")



try_ex_falso :: Context -> Measure_t -> Maybe Measure_t
try_ex_falso context measure = let nmeasure = newmeasure measure (Aspn (Atomic (Predicate bot_c [])) Fresh) bot_c in
                                 try_context_assumptions context bot_c nmeasure

  
try_context_assumptions :: Context -> Name Predicate -> Measure_t -> Maybe Measure_t
try_context_assumptions context p measure =
  Set.foldl (try_assumptions context p measure)
            (Just (MError "No assumption brought progress"))
            (to_assumptions context)


try_assumptions :: Context -> Name Predicate -> Measure_t -> Maybe Measure_t -> Assumption_t -> Maybe Measure_t
try_assumptions context goal measure Nothing tformula = try_assumption tformula goal context measure
try_assumptions context goal measure (Just (MError _)) tformula = try_assumption tformula goal context measure
try_assumptions context goal measure (Just (MInt n)) tformula = Just (MInt n)

try_assumption :: Assumption_t -> Name Predicate -> Context -> Measure_t -> Maybe Measure_t
try_assumption (Aspn phi md) goal context measure =
  if (goal_matches (Aspn phi md) goal)
  then
    let nmeasure = (newmeasure measure (Aspn phi md) goal) in
      (Prelude.foldl (\ sofar phiarg ->
                         case sofar of
                           Nothing -> Nothing
                           Just (MError s) -> Just (MError s)
                           Just (MInt _) -> prover context phiarg nmeasure)
                     (Just nmeasure)
                     (get_args phi))
  else Nothing

