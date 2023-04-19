module Main where

import qualified Prelude
import qualified Debug.Trace

(++) = (Prelude.++)

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f5 _ =
  f5

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f5 f6 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f5)
    (\n0 -> f6 n0 (nat_rect f5 f6 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f5 f6 l =
  case l of {
   ([]) -> f5;
   (:) y l0 -> f6 y l0 (list_rect f5 f6 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

length :: (([]) a1) -> Prelude.Integer
length l =
  case l of {
   ([]) -> 0;
   (:) _ l' -> Prelude.succ (length l')}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f5 s =
  f5 s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

in_dec :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> Prelude.Bool
in_dec h a l =
  list_rec Prelude.False (\a0 _ iHl ->
    let {s = h a0 a} in
    case s of {
     Prelude.True -> Prelude.True;
     Prelude.False -> iHl}) l

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map = Prelude.map

flat_map :: (a1 -> ([]) a2) -> (([]) a1) -> ([]) a2
flat_map f5 l =
  case l of {
   ([]) -> ([]);
   (:) x t -> app (f5 x) (flat_map f5 t)}

fold_right :: (a2 -> a1 -> a1) -> a1 -> (([]) a2) -> a1
fold_right = Prelude.foldr

nodup :: (a1 -> a1 -> Prelude.Bool) -> (([]) a1) -> ([]) a1
nodup decA l =
  case l of {
   ([]) -> ([]);
   (:) x xs ->
    case in_dec decA x xs of {
     Prelude.True -> nodup decA xs;
     Prelude.False -> (:) x (nodup decA xs)}}

type Set a = ([]) a

set_add :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (Set a1) -> Set a1
set_add aeq_dec a x =
  case x of {
   ([]) -> (:) a ([]);
   (:) a1 x1 ->
    case aeq_dec a a1 of {
     Prelude.True -> (:) a1 x1;
     Prelude.False -> (:) a1 (set_add aeq_dec a x1)}}

set_mem :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (Set a1) -> Prelude.Bool
set_mem aeq_dec a x =
  case x of {
   ([]) -> Prelude.False;
   (:) a1 x1 ->
    case aeq_dec a a1 of {
     Prelude.True -> Prelude.True;
     Prelude.False -> set_mem aeq_dec a x1}}

set_union :: (a1 -> a1 -> Prelude.Bool) -> (Set a1) -> (Set a1) -> Set a1
set_union aeq_dec x y =
  case y of {
   ([]) -> x;
   (:) a1 y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)}

set_diff :: (a1 -> a1 -> Prelude.Bool) -> (Set a1) -> (Set a1) -> Set a1
set_diff aeq_dec x y =
  case x of {
   ([]) -> ([]);
   (:) a1 x1 ->
    case set_mem aeq_dec a1 y of {
     Prelude.True -> set_diff aeq_dec x1 y;
     Prelude.False -> set_add aeq_dec a1 (set_diff aeq_dec x1 y)}}

lt_eq_lt_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Maybe
                Prelude.Bool
lt_eq_lt_dec n m =
  nat_rec (\m0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.Just Prelude.False)
      (\_ -> Prelude.Just Prelude.True)
      m0) (\_ iHn m0 ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.Nothing)
      (\n0 -> iHn n0)
      m0) n m

le_lt_eq_dec :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
le_lt_eq_dec n m =
  let {s = lt_eq_lt_dec n m} in
  case s of {
   Prelude.Just a -> a;
   Prelude.Nothing -> false_rec}

incl_dec :: (a1 -> a1 -> Prelude.Bool) -> (Set a1) -> (Set a1) ->
            Prelude.Bool
incl_dec dec v w =
  list_rec Prelude.True (\h _ iHt ->
    let {s = in_dec dec h w} in
    case s of {
     Prelude.True -> iHt;
     Prelude.False -> Prelude.False}) v

data Ninfty =
   Infty
 | Fin Prelude.Integer
 deriving (Prelude.Show)

sinfty :: Ninfty -> Ninfty
sinfty x =
  case x of {
   Infty -> Infty;
   Fin n -> Fin (Prelude.succ n)}

type Frontier = Prelude.String -> Ninfty

frontier_fin_0 :: Frontier
frontier_fin_0 _ =
  Fin 0

frontier_infty :: Frontier
frontier_infty _ =
  Infty

update_infty_V :: (Set Prelude.String) -> Frontier -> Frontier
update_infty_V v f5 x =
  case set_mem
         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
         v of {
   Prelude.True -> Infty;
   Prelude.False -> f5 x}

data Atom0 =
   Atom Prelude.String Prelude.Integer

atom_true :: Atom0 -> Frontier -> Prelude.Bool
atom_true a f5 =
  case a of {
   Atom x k ->
    case f5 x of {
     Infty -> Prelude.True;
     Fin n -> (Prelude.<=) k n}}

shift_atom :: Prelude.Integer -> Atom0 -> Atom0
shift_atom n a =
  case a of {
   Atom x k -> Atom x ((Prelude.+) n k)}

data Clause0 =
   Clause (Set Atom0) Atom0

clause_true :: Clause0 -> Frontier -> Prelude.Bool
clause_true c f5 =
  case c of {
   Clause conds conc ->
    case fold_right (Prelude.&&) Prelude.True
           (map (\a -> atom_true a f5) conds) of {
     Prelude.True -> atom_true conc f5;
     Prelude.False -> Prelude.True}}

shift_clause :: Prelude.Integer -> Clause0 -> Clause0
shift_clause n c =
  case c of {
   Clause conds conc -> Clause (map (shift_atom n) conds) (shift_atom n conc)}

all_shifts_true :: Clause0 -> Frontier -> Prelude.Bool
all_shifts_true c f5 =
  case c of {
   Clause _ conc ->
    case conc of {
     Atom x k ->
      case f5 x of {
       Infty -> Prelude.True;
       Fin n ->
        clause_true (shift_clause (sub ((Prelude.+) n (Prelude.succ 0)) k) c)
          f5}}}

vars_set_atom :: (Set Atom0) -> Set Prelude.String
vars_set_atom s =
  case s of {
   ([]) -> ([]);
   (:) a t ->
    case a of {
     Atom x _ ->
      let {cl = vars_set_atom t} in
      set_add
        ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
        cl}}

vars_clause :: Clause0 -> Set Prelude.String
vars_clause c =
  case c of {
   Clause conds a ->
    case a of {
     Atom x _ ->
      set_add
        ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
        (vars_set_atom conds)}}

vars :: (Set Clause0) -> Set Prelude.String
vars cs5 =
  flat_map vars_clause cs5

sub_vars_improvable :: (Set Clause0) -> (Set Prelude.String) -> (Set
                       Prelude.String) -> Frontier -> Set Prelude.String
sub_vars_improvable cs5 v w f5 =
  case cs5 of {
   ([]) -> ([]);
   (:) c t ->
    case c of {
     Clause l a ->
      case a of {
       Atom x k ->
        case (Prelude.||)
               ((Prelude.||)
                 (Prelude.not
                   (set_mem
                     ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                     x w))
                 (Prelude.not
                   (fold_right (Prelude.&&) Prelude.True
                     (map (\x0 ->
                       set_mem
                         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                         x0 v) (vars_set_atom l)))))
               (all_shifts_true (Clause l (Atom x k)) f5) of {
         Prelude.True -> sub_vars_improvable t v w f5;
         Prelude.False ->
          set_add
            ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x (sub_vars_improvable t v w f5)}}}}

type Ex_lfp_geq_S = Frontier

type Ex_lfp_geq = Ex_lfp_geq_S

ex_lfp_geq_incl :: (Set Clause0) -> (Set Prelude.String) -> (Set
                   Prelude.String) -> Frontier -> Ex_lfp_geq -> Ex_lfp_geq
ex_lfp_geq_incl _ _ _ _ h0 =
  h0

ex_lfp_geq_monotone :: (Set Clause0) -> (Set Prelude.String) -> Frontier ->
                       Frontier -> Ex_lfp_geq -> Ex_lfp_geq
ex_lfp_geq_monotone _ _ _ _ h =
  h

ex_lfp_geq_empty :: (Set Clause0) -> Frontier -> Ex_lfp_geq
ex_lfp_geq_empty _ f5 =
  f5

ex_lfp_geq_nodup_iff :: (Set Clause0) -> (Set Prelude.String) -> Frontier ->
                        (,) (Ex_lfp_geq -> Ex_lfp_geq)
                        (Ex_lfp_geq -> Ex_lfp_geq)
ex_lfp_geq_nodup_iff _ _ _ =
  (,) (\h -> sig_rec (\x _ -> x) h) (\h -> sig_rec (\x _ -> x) h)

sub_forward :: (Set Clause0) -> (Set Prelude.String) -> (Set Prelude.String)
               -> Frontier -> (,) (Set Prelude.String) Frontier
sub_forward cs5 v w f5 =
  let {x = sub_vars_improvable cs5 v w f5} in
  let {
   f' = \v0 ->
    case set_mem
           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           v0 x of {
     Prelude.True -> sinfty (f5 v0);
     Prelude.False -> f5 v0}}
  in
  (,) x f'

type Pre_thm = () -> () -> () -> Ex_lfp_geq -> Ex_lfp_geq

lem_33 :: (Set Clause0) -> (Set Prelude.String) -> (Set Prelude.String) ->
          Frontier -> ((Set Clause0) -> (Set Prelude.String) -> (Set
          Prelude.String) -> Frontier -> Prelude.Integer -> Pre_thm) ->
          Ex_lfp_geq -> Ex_lfp_geq
lem_33 _ _ _ _ _ x =
    x

thm_32 :: Prelude.Integer -> Prelude.Integer -> (Set Clause0) -> (Set
          Prelude.String) -> (Set Prelude.String) -> Frontier -> Ex_lfp_geq
          -> Ex_lfp_geq
thm_32 n m cs5 v w f5 x =
  nat_rect (\_ _ _ _ f6 _ _ _ _ -> f6) (\n0 iHn m0 ->
    Debug.Trace.trace
        ("IHn: n = " ++ Prelude.show n0 ++ ", m = " ++ Prelude.show m0 ++
        ", v = " ++ (Prelude.show v) ++ ", w = " ++ (Prelude.show w) ++
        Prelude.concatMap (\var -> ", f(" ++ var ++ ") = " ++ Prelude.show (f5 var)) v) Prelude.$
    nat_rect (\cs6 v0 w0 f6 _ _ _ h2 ->
      ex_lfp_geq_incl cs6
        (nodup
          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          v0)
        (nodup
          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          w0) f6 h2) (\m1 iHm cs6 v0 w0 f6 _ _ _ h2 ->
            Debug.Trace.trace
                 ("IHm: n = " ++ Prelude.show (Prelude.succ n0) ++ ", m = " ++ Prelude.show m1 ++
                 ", v = " ++ (Prelude.show v0) ++ ", w = " ++ (Prelude.show w0) ++
                 Prelude.concatMap (\var -> ", f(" ++ var ++ ") = " ++ Prelude.show (f6 var)) v) Prelude.$
      let {
        h3 =
         let {arg1 =
           (length
             (set_diff
               ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
               (nodup
                 ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 v0)
               (nodup
                 ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 w0)))}
         in let {arg2 = (Prelude.succ m1)}
         in
             (Debug.Trace.trace ("le_lt_eq_dec: n = " ++ Prelude.show arg1 ++ ", m = " ++ Prelude.show arg2)) (le_lt_eq_dec arg1 arg2)}

      in
      case h3 of {
       Prelude.True -> iHm cs6 v0 w0 f6 __ __ __ h2;
       Prelude.False ->
        let {h5 = iHn n0 cs6 w0 ([]) f6 __ __ __ f6} in
        let {
         h = lem_33 cs6 v0
               (nodup
                 ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 w0) f6 (\cs' v' w' f' m2 _ _ _ h9 ->
               iHn m2 cs' v' w' f' __ __ __ h9)
               (eq_rec_r
                 (nodup
                   ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   w0) h5
                 (nodup
                   ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   (nodup
                     ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                     w0)))}
        in
        sig_rec (\h0 _ ->
          let {
           p = sub_forward cs6
                 (nodup
                   ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   v0)
                 (nodup
                   ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                   v0) h0}
          in
          case p of {
           (,) a b ->
            eq_rect
              (sub_vars_improvable cs6
                (nodup
                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  v0)
                (nodup
                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  v0) h0) (\_ ->
              eq_rect (\v1 ->
                case set_mem
                       ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                       v1
                       (sub_vars_improvable cs6
                         (nodup
                           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           v0)
                         (nodup
                           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           v0) h0) of {
                 Prelude.True -> sinfty (h0 v1);
                 Prelude.False -> h0 v1})
                (case a of {
                  ([]) -> h0;
                  (:) _ _ ->
                   let {
                    s = incl_dec
                          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                          v0
                          (nodup
                            ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                            (set_union
                              ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                              (nodup
                                ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                                w0) a))}
                   in
                   case s of {
                    Prelude.True -> update_infty_V v0 f6;
                    Prelude.False ->
                     ex_lfp_geq_monotone cs6
                       (nodup
                         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                         v0) b f6
                       (iHm cs6 v0
                         (nodup
                           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           (set_union
                             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             w0 a)) b __ __ __
                         (iHn n0 cs6
                           (nodup
                             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             (set_union
                               ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                               w0 a)) ([]) b __ __ __ b))}}) b) a __}) h}) m0)
    n m cs5 v w f5 __ __ __ x

cs :: ([]) Clause0
cs =
  (:) (Clause ((:) (Atom "a" 0) ([])) (Atom "b" (Prelude.succ (Prelude.succ
    0)))) ((:) (Clause ((:) (Atom "b" (Prelude.succ (Prelude.succ 0))) ([]))
    (Atom "c" (Prelude.succ 0))) ([]))

f :: Frontier
f =
  frontier_fin_0

vars' :: ([]) Prelude.String
vars' =
  nodup ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
    (vars cs)

ex_fail0 :: Ex_lfp_geq -> Ex_lfp_geq
ex_fail0 x =
  thm_32 (length vars') (length vars') cs vars' ([]) f x

ex_lfp_geq_empty_fail0 :: Ex_lfp_geq
ex_lfp_geq_empty_fail0 =
  ex_lfp_geq_empty cs f

cs0 :: ([]) Clause0
cs0 =
  (:) (Clause ((:) (Atom "a" 0) ([])) (Atom "b" (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))) ((:) (Clause ((:) (Atom "b" (Prelude.succ
    (Prelude.succ 0))) ([])) (Atom "c" (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))) ([]))

f0 :: Frontier
f0 =
  frontier_fin_0

vars'0 :: ([]) Prelude.String
vars'0 =
  nodup ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
    (vars cs0)

ex_fail1 :: Ex_lfp_geq -> Ex_lfp_geq
ex_fail1 x =
  thm_32 (length vars'0) (length vars'0) cs0 vars'0 ([]) f0 x

ex_lfp_geq_empty_fail1 :: Ex_lfp_geq
ex_lfp_geq_empty_fail1 =
  ex_lfp_geq_empty cs0 f0

cs1 :: ([]) Clause0
cs1 =
  (:) (Clause ((:) (Atom "a" 0) ([])) (Atom "b" (Prelude.succ (Prelude.succ
    (Prelude.succ 0))))) ((:) (Clause ((:) (Atom "b" (Prelude.succ
    (Prelude.succ (Prelude.succ (Prelude.succ 0))))) ([])) (Atom "c"
    (Prelude.succ 0))) ([]))

f1 :: Frontier
f1 =
  frontier_fin_0

vars'1 :: ([]) Prelude.String
vars'1 =
  nodup ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
    (vars cs1)

ex_fail2 :: Ex_lfp_geq -> Ex_lfp_geq
ex_fail2 x =
  thm_32 (length vars'1) (length vars'1) cs1 vars'1 ([]) f1 x

ex_lfp_geq_empty_fail2 :: Ex_lfp_geq
ex_lfp_geq_empty_fail2 =
  ex_lfp_geq_empty cs1 f1

cs2 :: ([]) Clause0
cs2 =
  (:) (Clause ((:) (Atom "a" 0) ([])) (Atom "b" (Prelude.succ (Prelude.succ
    0)))) ((:) (Clause ((:) (Atom "b" (Prelude.succ (Prelude.succ 0))) ([]))
    (Atom "a" (Prelude.succ 0))) ([]))

f2 :: Frontier
f2 =
  frontier_fin_0

vars'2 :: ([]) Prelude.String
vars'2 =
  nodup ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
    (vars cs2)

ex_fail3 :: Ex_lfp_geq -> Ex_lfp_geq
ex_fail3 x =
  thm_32 (length vars'2) (length vars'2) cs2 vars'2 ([]) f2 x

ex_lfp_geq_empty_fail3 :: Ex_lfp_geq
ex_lfp_geq_empty_fail3 =
  ex_lfp_geq_empty cs2 f2

cs3 :: ([]) Clause0
cs3 =
  (:) (Clause ((:) (Atom "a" 0) ([])) (Atom "b" 0)) ((:) (Clause ((:) (Atom
    "b" (Prelude.succ (Prelude.succ (Prelude.succ 0)))) ([])) (Atom "c"
    (Prelude.succ (Prelude.succ (Prelude.succ 0))))) ([]))

f3 :: Frontier
f3 =
  frontier_infty

vars'3 :: ([]) Prelude.String
vars'3 =
  nodup ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
    (vars cs3)

ex_fail4 :: Ex_lfp_geq -> Ex_lfp_geq
ex_fail4 x =
  thm_32 (length vars'3) (length vars'3) cs3 vars'3 ([]) f3 x

ex_lfp_geq_empty_fail4 :: Ex_lfp_geq
ex_lfp_geq_empty_fail4 =
  ex_lfp_geq_empty cs3 f3

cs4 :: ([]) Clause0
cs4 =
  (:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "max_case_strong.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([]))
    (Atom "max_case_strong.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "min_case_strong.u0" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "min_case_strong.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality.u1" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionality.u1" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionality.u1" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionality.u3" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionalityS.u1" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "hypo.u0" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Set" 0) ([])) (Atom "Prop" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "SetoidTactics.DefaultRelation.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "SetoidTactics.default_relation.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "SetoidTactics.equivalence_default.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "GenericMinMax.gmax.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "GenericMinMax.gmin.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Private_Dec.max_case_strong.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Private_Dec.max_case.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Private_Dec.min_case_strong.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Private_Dec.min_case.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "max_case_strong.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "max_case.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "min_case_strong.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "min_case.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Relations.Relation_Operators.1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.2" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Operators.3" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.4" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Operators.5" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.6" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Operators.7" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.8" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Operators.9" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.10" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Operators.11" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.14" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Operators.15" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.16" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "FunctionalExtensionality.equal_f.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.equal_f.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "FunctionalExtensionality.equal_f_dep.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.equal_f_dep.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_extensionality.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_extensionality.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_extensionality.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_extensionality.u3" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_extensionalityP.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_extensionalityS.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_extensionalityS.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_eq_rect.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_eq_rect.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_eq_rect.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.eta_expansion_dep.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.eta_expansion_dep.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.eta_expansion.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.eta_expansion.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.QArith.QArith_base.52" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.QArith.QArith_base.54" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.setoid_ring.InitialRing.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.32" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.InitialRing.49" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.70" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.InitialRing.71" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "hypo.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.OrderedRing.1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.micromega.OrderedRing.21" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Classes.RelationClasses.1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "RelationClasses.Tlist.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Classes.RelationClasses.43" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "RelationClasses.arrows.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "RelationClasses.arrows.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RelationClasses.unary_operation.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "RelationClasses.binary_operation.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RelationClasses.ternary_operation.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "RelationClasses.unary_predicate.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_relation.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "RelationClasses.pointwise_extension.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Classes.RelationClasses.67" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom
    "RelationClasses.subrelation_partial_order_obligation_1.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.RingMicromega.1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.micromega.RingMicromega.2" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.RingMicromega.3" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.micromega.RingMicromega.9" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.RingMicromega.12" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "RingMicromega.map_option.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RingMicromega.map_option.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "RingMicromega.map_option2.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RingMicromega.map_option2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "RingMicromega.map_option2.u2" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.RingMicromega.47" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "RingMicromega.Formula.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "RingMicromega.cnf_of_list.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_of_list_correct.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "RingMicromega.cnf_normalise.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_negate.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "RingMicromega.cnf_normalise_correct.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_negate_correct.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.micromega.RingMicromega.98" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Structures.OrdersFacts.34" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Morphisms_Prop.ex_iff_morphism_obligation_1.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.ex_impl_morphism_obligation_1.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.ex_flip_impl_morphism_obligation_1.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.all_iff_morphism_obligation_1.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.all_impl_morphism_obligation_1.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.all_flip_impl_morphism_obligation_1.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.Acc_pt_morphism.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Morphisms_Prop.Acc_rel_morphism.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.well_founded_morphism.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "DeclConstant.DeclaredConstant.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "DeclConstant.GT.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "DeclConstant.GT_O.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "DeclConstant.GT_APP1.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "DeclConstant.GT_APP1.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "DeclConstant.GT_APP2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "DeclConstant.GT_APP2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "DeclConstant.GT_APP2.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "PLF.Ul.2" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "PLF.Ul.4" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "PLF.Ul.6" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Wf.1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "Coq.Init.Wf.2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "well_founded_induction_type.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Wf.4" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Wf.5" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Wf.6" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Wf.7" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "total_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "t_empty.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "t_update.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "t_apply_empty.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "t_update_eq.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "t_update_neq.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "t_update_shadow.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "t_update_same.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "t_update_permute.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "partial_map.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "empty.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "update.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "apply_empty.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "update_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "update_neq.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "update_shadow.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "update_same.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "update_permute.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "inclusion.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "inclusion_update.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "iter.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "if_negb.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "andb_if.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "negb_if.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Bool.Bool.56" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Init.Byte.258" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.13" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "app_nil_r.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "app_nil_r.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "app_assoc.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "app_assoc.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "app_eq_app.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.44" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "nth_split.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "nth_ext.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "nth_error_split.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "remove_app.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "notin_remove.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.318" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.319" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "concat_map.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "concat_map.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "remove_concat.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "map_id.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "map_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "map_map.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "map_map.u2" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "map_ext_in.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "map_ext_in.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ext_in_map.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ext_in_map.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "map_ext_in_iff.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "map_ext_in_iff.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "map_ext.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "map_ext.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "flat_map_ext.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "flat_map_ext.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "nth_nth_nth_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.377" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.378" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "fold_left_length.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.381" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.382" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "fold_right_app.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "fold_right_app.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "fold_left_rev_right.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "fold_left_rev_right.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "fold_symmetric.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "list_power.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "list_power.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.400" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.454" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "filter_ext_in.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "remove_alt.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.465" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.466" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "split_combine.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.477" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.479" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "incl_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "incl_map.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.495" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "firstn_all2.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "firstn_app.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "firstn_firstn.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "firstn_skipn.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "firstn_skipn_rev.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.572" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "firstn_map.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "firstn_map.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "firstn_map.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "firstn_map.u3" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.581" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.582" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Add_split.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Add_split.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.615" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "NoDup_map_inv.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "NoDup_map_inv.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Forall_rect.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "map_ext_Forall.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Exists_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Exists_map.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Exists_concat.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Exists_flat_map.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Exists_flat_map.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Forall_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Forall_map.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Forall_concat.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Forall_flat_map.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Forall_flat_map.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "exists_Forall.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "exists_Forall.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Forall_image.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Forall_image.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "concat_nil_Forall.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "in_flat_map_Exists.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "in_flat_map_Exists.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "notin_flat_map_Forall.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "notin_flat_map_Forall.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Lists.List.821" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.838" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.857" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "repeat_cons.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "count_occ_unique.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "repeat_to_concat.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Init.Logic.2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Logic.3" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ex.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ex2.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "all.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Logic.7"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq_sind_r.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_rec_r.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_rect_r.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.16" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.17" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "f_equal_dep2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal_dep2.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal_dep2.u2"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "f_equal_dep2.u3" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "rew_opp_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "rew_opp_r.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "rew_opp_l.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "rew_opp_l.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal2.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal2.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal2.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "f_equal3.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "f_equal3.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "f_equal3.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "f_equal3.u3" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "f_equal4.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "f_equal4.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal4.u2" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal4.u3" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal4.u4" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "f_equal5.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "f_equal5.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "f_equal5.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "f_equal5.u3" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "f_equal5.u4" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "f_equal5.u5" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "f_equal_compose.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "f_equal_compose.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "f_equal_compose.u2" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq_trans_refl_l.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_trans_refl_r.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sym_involutive.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_trans_sym_inv_l.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_trans_sym_inv_r.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_trans_assoc.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "rew_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "rew_map.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "rew_map.u2" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_trans_map.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_trans_map.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "map_subst.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "map_subst.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "map_subst.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "map_subst_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "map_subst_map.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "map_subst_map.u2" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "map_subst_map.u3"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "rew_swap.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "rew_swap.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "rew_compose.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "rew_compose.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_id_comm_l.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_id_comm_r.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_refl_map_distr.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_refl_map_distr.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_trans_map_distr.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_trans_map_distr.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sym_map_distr.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sym_map_distr.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_trans_sym_distr.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_trans_rew_distr.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_trans_rew_distr.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "rew_const.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "rew_const.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "subrelation.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "subrelation.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "unique.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "uniqueness.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "unique_existence.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "forall_exists_unique_domain_coincide.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "forall_exists_coincide_unique_domain.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "inhabited.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "exists_inhabited.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "inhabited_covariant.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "inhabited_covariant.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_stepl.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ex_rect.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_ex_intro_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_ex_intro.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_ex_rect.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_ex_rect_ex_intro_l.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_ex_rect_ex_intro_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_ex_rect_ex_intro.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_ex_rect_uncurried.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_ex_intro_hprop.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "rew_ex.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "ex2_rect.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_ex_intro2_uncurried.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_ex_intro2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_ex_intro2_hprop_nondep.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq_ex_intro2_hprop.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_ex2_rect.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_ex2_rect_ex_intro2_l.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_ex2_rect_ex_intro2_r.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_ex2_rect_ex_intro2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_ex2_rect_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "rew_ex2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "nat_rect_succ_r.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "nat_rect_plus.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Nnat.N2Nat.inj_iter.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Nnat.Nat2N.inj_iter.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Pnat.Pos2Nat.inj_iter.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sig.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.3" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "sig2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.6" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.10" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT2.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.15" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Specif.21" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "sig_of_sigT.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT_of_sig.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sig2_of_sigT2.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "sigT2_of_sig2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "ex_of_sig.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ex_of_sigT.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "ex2_of_sig2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ex2_of_sigT2.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT_eta.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "sigT_eta.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "sig_eta.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "sigT2_eta.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "sigT2_eta.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "sigT2_eta.u2" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "sig2_eta.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "exists_to_inhabited_sig.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "inhabited_sig_to_exists.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.78" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "projT1_eq.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "projT1_eq.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "projT2_eq.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "projT2_eq.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "eq_existT_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq_existT_uncurried.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_uncurried.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_uncurried.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT_curried.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT_curried.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_existT_curried_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT_curried_map.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT_curried_map.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_existT_curried_map.u3" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT_curried_trans.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT_curried_trans.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_existT_curried_congr.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT_curried_congr.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT_l.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_existT_l.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq_existT_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT_r.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sigT_hprop.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_hprop.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_uncurried_iff.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_uncurried_iff.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_rect.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_rect.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_rect.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq_sigT_rec.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_rec.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sigT_ind.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_ind.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_rect_existT_l.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_rect_existT_l.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_rect_existT_l.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_rect_existT_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_rect_existT_r.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_rect_existT_r.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_rect_existT.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_rect_existT.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_rect_existT.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_rect_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_rect_uncurried.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_rect_uncurried.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_rec_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_rec_uncurried.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_ind_uncurried.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_ind_uncurried.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT_hprop_iff.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT_hprop_iff.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT_nondep.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq_sigT_nondep.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "rew_sigT.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "rew_sigT.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "proj1_sig_eq.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "proj2_sig_eq.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_exist_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig_uncurried.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_exist_curried.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_exist_l.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "eq_exist_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig_rect.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sig_rect.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig_rec.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig_ind.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig_rect_exist_l.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig_rect_exist_l.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig_rect_exist_r.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig_rect_exist_r.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig_rect_exist.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig_rect_exist.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig_rect_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig_rect_uncurried.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig_rec_uncurried.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig_ind_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig_hprop.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sig_uncurried_iff.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig_hprop_iff.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "rew_sig.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "rew_sig.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "sigT_of_sigT2_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2_eq.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sigT_of_sigT2_eq.u2" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "projT1_of_sigT2_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "projT1_of_sigT2_eq.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "projT1_of_sigT2_eq.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "projT2_of_sigT2_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "projT2_of_sigT2_eq.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "projT2_of_sigT2_eq.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "projT3_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "projT3_eq.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "projT3_eq.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT2_uncurried.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT2_uncurried.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_existT2_uncurried.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_uncurried.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_uncurried.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_uncurried.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT2_curried.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT2_curried.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_existT2_curried.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq_sigT2.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sigT2.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT2_l.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_existT2_l.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_existT2_l.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq_existT2_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_existT2_r.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_existT2_r.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_hprop.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_hprop.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq_sigT2_hprop.u2" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq_sigT2_uncurried_iff.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_uncurried_iff.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_uncurried_iff.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect.u2" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect.u3"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rec.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq_sigT2_rec.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rec.u2" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sigT2_ind.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_ind.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_ind.u2"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_existT2_l.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect_existT2_l.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect_existT2_l.u2"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_existT2_l.u3" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect_existT2_r.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect_existT2_r.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_existT2_r.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect_existT2_r.u3" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect_existT2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_existT2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect_existT2.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect_existT2.u3" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect_uncurried.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rect_uncurried.u2"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_uncurried.u3" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_rec_uncurried.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_rec_uncurried.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_rec_uncurried.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_ind_uncurried.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_ind_uncurried.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_ind_uncurried.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_hprop_iff.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_hprop_iff.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_hprop_iff.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sigT2_nondep.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sigT2_nondep.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sigT2_nondep.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "rew_sigT2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "rew_sigT2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "sig_of_sig2_eq.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "proj1_sig_of_sig2_eq.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "proj2_sig_of_sig2_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "proj3_sig_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_exist2_uncurried.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_uncurried.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_exist2_curried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq_exist2_l.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_exist2_r.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_hprop.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig2_uncurried_iff.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig2_rect.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq_sig2_rect.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_rec.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_ind.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig2_rect_exist2_l.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig2_rect_exist2_l.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_rect_exist2_r.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig2_rect_exist2_r.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig2_rect_exist2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_rect_exist2.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig2_rect_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig2_rect_uncurried.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_rec_uncurried.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq_sig2_ind_uncurried.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq_sig2_hprop_iff.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_sig2_nondep.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "rew_sig2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "rew_sig2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.759" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "sumor.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.762" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Specif.771" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Wf_Z.natlike_rec2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Wf_Z.natlike_rec3.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Wf_Z.Zlt_0_rec.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Wf_Z.Z_lt_rec.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Wf_Z.Zlt_lower_bound_rec.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Zabs.Zabs_intro.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Arith.Wf_nat.1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "induction_ltof1.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "induction_gtof1.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "induction_ltof2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "induction_gtof2.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "lt_wf_rect1.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "lt_wf_rect.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "gt_wf_rect.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "lt_wf_double_rect.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "has_unique_least_element.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Zmisc.iter_nat_of_Z.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinNat.N.binary_rect.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinNat.N.peano_rect.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinNat.N.peano_rect_base.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "BinNat.N.peano_rect_succ.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinNat.N.recursion.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinNat.N.recursion_wd.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinNat.N.recursion_0.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinNat.N.recursion_succ.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinNat.N.iter_swap_gen.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinNat.N.iter_swap_gen.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinNat.N.iter_swap.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinNat.N.iter_succ.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinNat.N.iter_succ_r.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinNat.N.iter_add.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinNat.N.iter_ind.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinNat.N.iter_invariant.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinPos.Pos.peano_rect.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinPos.Pos.peano_rect_succ.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "BinPos.Pos.peano_rect_base.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.PArith.BinPos.78"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinPos.Pos.PeanoView_iter.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "BinPos.Pos.eq_dep_eq_positive.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinPos.Pos.peano_equiv.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinPos.Pos.iter_swap_gen.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinPos.Pos.iter_swap_gen.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_swap.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinPos.Pos.iter_succ.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinPos.Pos.iter_succ_r.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_add.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinPos.Pos.iter_ind.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinPos.Pos.iter_invariant.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_op_succ.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Init.Unconvertible.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Decimal.13" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Strings.Ascii.2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Basics.compose.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Basics.compose.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Basics.compose.u2" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Basics.arrow.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Basics.arrow.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Basics.const.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Basics.const.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Basics.flip.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Basics.flip.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Basics.flip.u2"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Basics.apply.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Basics.apply.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Vectors.Fin.3" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Fin.case0.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Fin.case0.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Fin.caseS'.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Fin.caseS'.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Fin.caseS.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "Fin.rectS.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Fin.rectS.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Fin.rect2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Fin.FS_inj.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Setoid.Seq_refl.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Setoid.Seq_sym.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Setoid.Seq_trans.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Strings.String.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Numbers.BinNums.1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Numbers.BinNums.2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Numbers.BinNums.3" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tactics.fix_proto.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.3" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.4" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.6" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.8" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "recursion.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "recursion_wd.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "recursion_0.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "recursion_succ.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Vectors.VectorEq.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.eqb_eq.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.cast.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.cast.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_rel_from_rel.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_relE.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "ssrunder.Under_rel.Over_rel.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.over_rel.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "ssrunder.Under_rel.over_rel_done.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.under_rel_done.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.8" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.9" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.ssr.ssrunder.10" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.ssr.ssrunder.11" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.12" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.ssr.ssrunder.13" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinNat.N.iter.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.PArith.BinPosDef.20" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_op.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "BinInt.Z.iter.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.3" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Init.Datatypes.5" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq_true_rect_r.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.11" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.14" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "option_map.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "option_map.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sum.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "sum.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.21" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Init.Datatypes.25" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.26" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.27" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "surjective_pairing.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "surjective_pairing.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "injective_projections.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "injective_projections.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "pair_equal_spec.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "pair_equal_spec.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "curry.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "curry.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "curry.u2" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "uncurry.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "uncurry.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "uncurry.u2" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "prod_uncurry_subdef.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "prod_uncurry_subdef.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "prod_uncurry_subdef.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "prod_curry_subdef.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "prod_curry_subdef.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "prod_curry_subdef.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "rew_pair.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "rew_pair.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "rew_pair.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Init.Datatypes.61" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "length.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.70"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.79" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "CompSpec.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "CompSpecT.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "CompSpecT.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "CompSpec2Type.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "identity.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.96" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ID.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Decidable.dec_functional_relation.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Decidable.dec_functional_relation.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.Logic.Eqdep_dec.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Eqdep_dec.eq_proofs_unicity.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Eqdep_dec.K_dec.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Eqdep_dec.inj_right_pair.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Eqdep_dec.K_dec_type.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Eqdep_dec.eq_rect_eq_dec.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Eqdep_dec.eq_rect_eq_dec.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Eqdep_dec.eq_dep_eq_dec.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Eqdep_dec.eq_dep_eq_dec.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Eqdep_dec.UIP_dec.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.14" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.Eqdep_dec.15" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Logic.Eqdep_dec.16" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.17" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.Eqdep_dec.18" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Logic.Eqdep_dec.19" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.20" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Eqdep_dec.inj_pair2_eq_dec.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Eqdep_dec.inj_pair2_eq_dec.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.respectful_hetero.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Morphisms.respectful_hetero.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.respectful_hetero.u2" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Morphisms.respectful_hetero.u3" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.11" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Morphisms.forall_def.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.Params.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Morphisms.proper_proper.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.76" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.flip_arrow.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Morphisms.flip_arrow.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Morphisms.proper_sym_flip.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_flip.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Morphisms.proper_sym_flip_2.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_flip_2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Morphisms.proper_sym_flip_2.u2" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Morphisms.proper_sym_impl_iff_2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff_2.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Morphisms.PartialOrder_proper.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.PartialOrder_StrictOrder.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Morphisms.StrictOrder_PreOrder.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Morphisms.StrictOrder_PartialOrder.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Arith.Peano_dec.1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Vectors.VectorDef.4" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.rectS.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.rectS.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.rectS.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.case0.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.case0.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Vector.case0.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.caseS.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.caseS.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.caseS.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.caseS'.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.caseS'.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.caseS'.u2" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.rect2.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.rect2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.rect2.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.hd.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.last.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.const.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.nth.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.nth_order.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.replace.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Vector.replace_order.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.uncons.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.shiftout.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.shiftin.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.shiftrepeat.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.take.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.trunc.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.append.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.splitat.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.rev_append_tail.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.rev_append.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.rev.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "Vector.map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.map.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Vector.map2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.map2.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.map2.u2"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.fold_left.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.fold_left.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.fold_right.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.fold_right.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.fold_right2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.fold_right2.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.fold_right2.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.fold_left2.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.fold_left2.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.fold_left2.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.Forall.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Vector.Exists.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.In.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.Forall2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.Forall2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.Exists2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.Exists2.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.of_list.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.micromega.Env.1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Refl.make_impl.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Refl.make_impl_true.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Refl.make_impl_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Refl.make_impl_map.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Refl.make_conj.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Refl.make_conj_cons.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Refl.make_conj_impl.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Refl.make_conj_in.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Refl.make_conj_app.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Refl.make_conj_rapp.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Refl.not_make_conj_cons.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Refl.not_make_conj_app.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.Ztac.12" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.4" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.Trace.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.micromega.Tauto.7" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.8" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.9" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.10" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.11" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.13" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.16" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.rtyp.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Tauto.eKind.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.BFormula.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.36" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.37" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.38" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.39" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.40" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.map_simpl.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.map_simpl.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Coq.micromega.Tauto.49" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.50" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.51"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.TFormula.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Tauto.TFormula.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.66" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.67" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.is_bool.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Tauto.is_bool.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.is_bool_inv.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.is_bool_inv.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Tauto.xcnf.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.ocons.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.126" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.127" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.148" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.149" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.if_same.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_and_xcnf.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf_and_xcnf.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.rxcnf_or_xcnf.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_or_xcnf.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf_impl_xcnf.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.rxcnf_impl_xcnf.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_iff_xcnf.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf_iff_xcnf.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.rxcnf_xcnf.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_xcnf.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.324" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Tauto.eval_bf.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Tauto.eval_bf_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Tauto.eval_bf_map.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "VarMap.t.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.VarMap.4"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.VarMap.5" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.ZCoeff.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EnvRing.PExpr.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.EnvRing.4" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "EnvRing.Pol.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.micromega.EnvRing.8" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.EnvRing.9" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.micromega.EnvRing.10" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.EnvRing.11" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.micromega.EnvRing.57" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "EnvRing.env_morph.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EnvRing.Pjump_add.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EnvRing.Mphi_morph.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ssrsetoid.compat_Reflexive.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Relations.inverse_image_of_equivalence.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Relations.inverse_image_of_equivalence.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Relations.inverse_image_of_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Relations.inverse_image_of_eq.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_polynom.2" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_polynom.3" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_polynom.5" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_polynom.54" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_polynom.198" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Field_theory.1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Field_theory.7" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Field_theory.10" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Field_theory.204" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Field_theory.SF2AF.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Field_theory.428" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.97" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.113" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.120" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ring_kind.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ring_kind.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ring_kind.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "Coq.setoid_ring.Ring_theory.156" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Zcomplements.Zlength_aux.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.ZArith.Zcomplements.5" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.3" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.4" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EqdepFacts.eq_sigT_eq_dep.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "EqdepFacts.eq_dep_eq_sigT.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_dep_eq_sigT.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "EqdepFacts.eq_sigT_iff_eq_dep.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "EqdepFacts.eq_sig_eq_dep.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_dep_eq_sig.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "EqdepFacts.eq_sig_iff_eq_dep.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_sig_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "EqdepFacts.eq_sigT_sig_eq.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.21" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "EqdepFacts.eq_sigT_fst.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EqdepFacts.eq_sigT_fst.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_snd.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "EqdepFacts.eq_sigT_snd.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EqdepFacts.eq_sig_fst.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sig_snd.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EqdepFacts.Eq_rect_eq_on.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_rect_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "EqdepFacts.Eq_dep_eq_on.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EqdepFacts.Eq_dep_eq.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep1_eq_on.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_rect_eq__eq_dep1_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.Streicher_K_on__eq_rect_eq_on.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EqdepFacts.UIP_shift_on.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.UIP_shift.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.71" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.Inj_dep_pair_on.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "EqdepFacts.Inj_dep_pair.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_dep_eq_on__inj_pair2_on.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.78" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.79" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.80" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.81" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.82" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.83" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.84" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.f_eq_dep.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "EqdepFacts.f_eq_dep.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "EqdepFacts.f_eq_dep.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_dep_non_dep.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "EqdepFacts.eq_dep_non_dep.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.f_eq_dep_non_dep.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "EqdepFacts.f_eq_dep_non_dep.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "EqdepFacts.f_eq_dep_non_dep.u2" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "notT.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic_Type.2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "identity_ind_r.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "identity_rec_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "identity_rect_r.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "identity_rect_r.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.InjTyp.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.InjTyp.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.BinOp.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.BinOp.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.BinOp.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.BinOp.u3" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.BinOp.u4" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.BinOp.u5" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.UnOp.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.UnOp.u1" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.UnOp.u2" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.UnOp.u3" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.CstOp.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.CstOp.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.BinRel.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.BinRel.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.BinOpSpec.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.BinOpSpec.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.BinOpSpec.u2" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.UnOpSpec.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.UnOpSpec.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.Saturate.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.injterm.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.injterm.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.mkapp2.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.mkapp2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.mkapp2.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.mkapp2.u3" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.mkapp2.u4" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.mkapp2.u5" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.mkapp.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.mkapp.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.mkapp.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZifyClasses.mkapp.u3" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZifyClasses.mkrel.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZifyClasses.mkrel.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.cons_inj.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.eta.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.eq_nth_iff.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.nth_order_hd.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.nth_order_tl.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.nth_order_last.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.nth_order_ext.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.shiftin_nth.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.shiftin_last.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.shiftrepeat_nth.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.shiftrepeat_last.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.nth_order_replace_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.nth_order_replace_neq.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.replace_id.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.replace_replace_eq.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.replace_replace_neq.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.const_nth.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.map_id.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.map_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.map_map.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.map_map.u2" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.map_ext_in.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.map_ext_in.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.map_ext.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.map_ext.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.nth_map.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.nth_map.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.nth_map2.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.nth_map2.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.nth_map2.u2" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.fold_left_right_assoc_eq.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.fold_left_right_assoc_eq.u1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Vector.take_O.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.take_idem.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.take_app.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "Vector.take_prf_irr.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Vector.uncons_cons.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.append_comm_cons.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.splitat_append.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.append_splitat.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.Forall_impl.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.Forall_forall.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.Forall_nth_order.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.Forall2_nth_order.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_of_list_opp.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.length_to_list.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.of_list_to_list_opp.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.to_list_nil.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.to_list_cons.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_hd.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.to_list_last.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.to_list_const.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_nth_order.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.to_list_tl.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.to_list_append.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_rev_append_tail.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Vector.to_list_rev_append.u0" 0) ([]))
    (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_rev.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.to_list_map.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.to_list_map.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_fold_left.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.to_list_fold_left.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_fold_right.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Vector.to_list_fold_right.u1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_Forall.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.to_list_Exists.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Vector.to_list_In.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.to_list_Forall2.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Vector.to_list_Forall2.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZArith_dec.Zcompare_rect.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Structures.OrdersTac.4" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.ZArith.Znumtheory.45" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.ZArith.Znumtheory.59" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.ZArith.Znumtheory.75" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "ZMicromega.cnf_of_list.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZMicromega.cnf_of_list_correct.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "ZMicromega.normalise.u0" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZMicromega.normalise_correct.u0" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "ZMicromega.negate.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "ZMicromega.negate_correct.u0"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ZMicromega.cnfZ.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "ZMicromega.cnfZ.u1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "ZMicromega.cnfZ.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.micromega.ZMicromega.77"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Relations.Operators_Properties.1" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Coq.setoid_ring.BinList.1" 0) ([])) (Atom
    "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Coq.ssr.ssrclasses.1"
    0) ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "ssrclasses.eq_Reflexive.u0" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Equivalence.equiv.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Equivalence.pequiv.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.equiv_reflexive_obligation_1.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.equiv_symmetric_obligation_1.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.equiv_transitive_obligation_1.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Equivalence.respecting.u0" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.respecting.u1" 0) ([])) (Atom "Set" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Equivalence.respecting.u2" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.respecting_equiv_obligation_1.u0" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.respecting_equiv_obligation_1.u1" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_reflexive.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Equivalence.pointwise_reflexive.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_symmetric.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Equivalence.pointwise_symmetric.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_transitive.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Equivalence.pointwise_transitive.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_equivalence.u0" 0) ([])) (Atom "Set" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "Equivalence.pointwise_equivalence.u1" 0)
    ([])) (Atom "Set" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Coq.Structures.Equalities.1" 0) ([])) (Atom "Set" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "Coq.Init.Hexadecimal.19" 0) ([])) (Atom "Set"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "app_nil_r.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "app_nil_r.u1" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "app_assoc.u0" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "app_assoc.u1" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "nth_split.u0" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "nth_ext.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "nth_error_split.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "remove_app.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "notin_remove.u0" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "filter_ext_in.u0" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "remove_alt.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "split_combine.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "firstn_all2.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "firstn_app.u0" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "firstn_firstn.u0" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "firstn_skipn.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "firstn_skipn_rev.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "firstn_map.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "firstn_map.u1" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "firstn_map.u2" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "firstn_map.u3" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Add_split.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Add_split.u1" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "repeat_cons.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "count_occ_unique.u0" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "repeat_to_concat.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "Fin.caseS'.u1" 0) ([])) (Atom
    "Fin.caseS'.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Vector.eqb_eq.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "Vector.caseS'.u2" 0) ([])) (Atom "Vector.caseS'.u1" (Prelude.succ 0)))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "EnvRing.env_morph.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EnvRing.Pjump_add.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "EnvRing.Mphi_morph.u0" (Prelude.succ 0))) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.eq_nth_iff.u0" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.replace_replace_neq.u0" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "Vector.fold_left_right_assoc_eq.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.fold_left_right_assoc_eq.u1" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "Vector.append_splitat.u0" (Prelude.succ
    0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.to_list_of_list_opp.u0" (Prelude.succ 0))) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "Vector.of_list_to_list_opp.u0"
    (Prelude.succ 0))) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.to_list_append.u0" (Prelude.succ 0))) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Vector.to_list_map.u1" (Prelude.succ 0))) ((:)
    (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "SetoidTactics.DefaultRelation.u0" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.DefaultRelation.u0" 0) ([])) (Atom
    "SetoidTactics.default_relation.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "SetoidTactics.default_relation.u0" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.DefaultRelation.u0" 0) ([])) (Atom
    "SetoidTactics.equivalence_default.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "SetoidTactics.equivalence_default.u0" 0)) ((:) (Clause ((:) (Atom
    "ex.u0" 0) ([])) (Atom "Coq.Relations.Relation_Definitions.1" 0)) ((:)
    (Clause ((:) (Atom "ex2.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Coq.Relations.Relation_Definitions.1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Relations.Relation_Definitions.1" 0))
    ((:) (Clause ((:) (Atom "Init.Unconvertible.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Coq.Relations.Relation_Definitions.1"
    0)) ((:) (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "ID.u0" 0) ([])) (Atom "Coq.Relations.Relation_Definitions.1" 0)) ((:)
    (Clause ((:) (Atom "Morphisms.respectful_hetero.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.respectful_hetero.u1" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.respectful_hetero.u2" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.respectful_hetero.u3" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.forall_def.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Private_Dec.max_case_strong.u0" 0) ([])) (Atom "Private_Dec.max_case.u0"
    0)) ((:) (Clause ((:) (Atom "Private_Dec.min_case_strong.u0" 0) ([]))
    (Atom "Private_Dec.min_case.u0" 0)) ((:) (Clause ((:) (Atom
    "Private_Dec.max_case_strong.u0" 0) ([])) (Atom "max_case_strong.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "max_case_strong.u0" 0)) ((:) (Clause ((:) (Atom "max_case_strong.u0" 0)
    ([])) (Atom "max_case.u0" 0)) ((:) (Clause ((:) (Atom
    "Private_Dec.min_case_strong.u0" 0) ([])) (Atom "min_case_strong.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "min_case_strong.u0" 0)) ((:) (Clause ((:) (Atom "min_case_strong.u0" 0)
    ([])) (Atom "min_case.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.3" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.4" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.5" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.6" 0)) ((:) (Clause ((:) (Atom "sum.u0"
    0) ([])) (Atom "Coq.Relations.Relation_Operators.7" 0)) ((:) (Clause ((:)
    (Atom "sum.u1" 0) ([])) (Atom "Coq.Relations.Relation_Operators.7" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.8" 0)) ((:) (Clause ((:) (Atom
    "sigT.u1" 0) ([])) (Atom "Coq.Relations.Relation_Operators.9" 0)) ((:)
    (Clause ((:) (Atom "Coq.Relations.Relation_Operators.8" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.10" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Coq.Relations.Relation_Operators.10" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.10" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Relations.Relation_Operators.10" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.78" 0) ([])) (Atom "Coq.Relations.Relation_Operators.10"
    0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.9" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.11" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Coq.Relations.Relation_Operators.11" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.11" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Relations.Relation_Operators.11" 0))
    ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.11" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.78" 0) ([])) (Atom "Coq.Relations.Relation_Operators.11"
    0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.11" 0)) ((:) (Clause ((:) (Atom
    "prod.u0" 0) ([])) (Atom "Coq.Relations.Relation_Operators.14" 0)) ((:)
    (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.15" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.14" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.16" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.15" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.16" 0)) ((:) (Clause ((:) (Atom
    "prod.u0" 0) ([])) (Atom "Coq.Relations.Relation_Operators.16" 0)) ((:)
    (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "Coq.Relations.Relation_Operators.16" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "FunctionalExtensionality.equal_f.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "FunctionalExtensionality.equal_f.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "FunctionalExtensionality.equal_f.u1" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "FunctionalExtensionality.equal_f.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "FunctionalExtensionality.equal_f_dep.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.equal_f_dep.u1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u1" 0)) ((:)
    (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u0" 0) ([]))
    (Atom "FunctionalExtensionality.functional_extensionality.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality.u0" 0)) ((:) (Clause
    ((:) (Atom "FunctionalExtensionality.functional_extensionality_dep.u1" 0)
    ([])) (Atom "FunctionalExtensionality.functional_extensionality.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality.u1" 0)) ((:) (Clause
    ((:) (Atom "FunctionalExtensionality.functional_extensionality.u0" 0)
    ([])) (Atom "FunctionalExtensionality.forall_extensionality.u0" 0)) ((:)
    (Clause ((:) (Atom "FunctionalExtensionality.forall_extensionality.u3" 0)
    ([])) (Atom "FunctionalExtensionality.forall_extensionality.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionality.u0" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.forall_extensionality.u3" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionality.u1" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.forall_extensionality.u1" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionality.u2" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.forall_extensionality.u3" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionality.u2" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.functional_extensionality.u0" 0) ([]))
    (Atom "FunctionalExtensionality.forall_extensionalityP.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionalityP.u0" 0)) ((:) (Clause
    ((:) (Atom "FunctionalExtensionality.functional_extensionality.u0" 0)
    ([])) (Atom "FunctionalExtensionality.forall_extensionalityS.u0" 0)) ((:)
    (Clause ((:) (Atom "FunctionalExtensionality.forall_extensionalityS.u1"
    0) ([])) (Atom "FunctionalExtensionality.forall_extensionalityS.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_extensionalityS.u0" 0)) ((:) (Clause
    ((:) (Atom "FunctionalExtensionality.functional_extensionality_dep.u0" 0)
    ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0)) ((:)
    (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u1" 0) ([]))
    (Atom "FunctionalExtensionality.functional_extensionality_dep_good.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u1" 0)) ((:)
    (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u0" 0) ([]))
    (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u0" 0))
    ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0) ([]))
    (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u0" 0))
    ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep.u1" 0) ([]))
    (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u1" 0))
    ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u1" 0) ([]))
    (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u1" 0))
    ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0) ([]))
    (Atom "FunctionalExtensionality.forall_sig_eq_rect.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "sig.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.functional_extensionality_dep_good.u1" 0)
    ([])) (Atom "FunctionalExtensionality.forall_sig_eq_rect.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u1" 0)) ((:) (Clause ((:)
    (Atom "sig.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u1" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.forall_sig_eq_rect.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "sig.u0" 0) ([])) (Atom "FunctionalExtensionality.forall_eq_rect.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u1" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect.u1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "FunctionalExtensionality.forall_eq_rect.u1" 0))
    ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect.u1" 0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.forall_sig_eq_rect.u2" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect.u2" 0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u0" 0)
    ([])) (Atom "FunctionalExtensionality.forall_eq_rect_comp.u0" 0)) ((:)
    (Clause ((:) (Atom "FunctionalExtensionality.forall_eq_rect.u0" 0) ([]))
    (Atom "FunctionalExtensionality.forall_eq_rect_comp.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u0" 0)) ((:) (Clause ((:)
    (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u1" 0)
    ([])) (Atom "FunctionalExtensionality.forall_eq_rect_comp.u1" 0)) ((:)
    (Clause ((:) (Atom "FunctionalExtensionality.forall_eq_rect.u1" 0) ([]))
    (Atom "FunctionalExtensionality.forall_eq_rect_comp.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u1" 0)) ((:) (Clause ((:)
    (Atom "sig.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u1" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.forall_eq_rect.u2" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u2" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.forall_eq_rect_comp.u2" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0)
    ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u0"
    0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u0" 0)
    ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u0"
    0)) ((:) (Clause ((:) (Atom "FunctionalExtensionality.forall_eq_rect.u0"
    0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u0"
    0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u1" 0) ([]))
    (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u1"
    0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good_refl.u1" 0)
    ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u1"
    0)) ((:) (Clause ((:) (Atom "FunctionalExtensionality.forall_eq_rect.u1"
    0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u1"
    0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u0" 0) ([]))
    (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u0"
    0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u0"
    0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u0"
    0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.functional_extensionality_dep_good.u1" 0) ([]))
    (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u1"
    0)) ((:) (Clause ((:) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good.u1"
    0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "FunctionalExtensionality.f_equal__functional_extensionality_dep_good__fun.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.eta_expansion_dep.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.eta_expansion_dep.u1" 0)) ((:) (Clause ((:)
    (Atom "FunctionalExtensionality.eta_expansion_dep.u0" 0) ([])) (Atom
    "FunctionalExtensionality.eta_expansion.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "FunctionalExtensionality.eta_expansion.u0" 0))
    ((:) (Clause ((:) (Atom "FunctionalExtensionality.eta_expansion_dep.u1"
    0) ([])) (Atom "FunctionalExtensionality.eta_expansion.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "FunctionalExtensionality.eta_expansion.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.1" 0)) ((:) (Clause ((:) (Atom
    "Setoid.Seq_refl.u0" 0) ([])) (Atom "Coq.setoid_ring.InitialRing.1" 0))
    ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.32" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.1" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.32" 0)) ((:) (Clause ((:) (Atom
    "Setoid.Seq_refl.u0" 0) ([])) (Atom "Coq.setoid_ring.InitialRing.32" 0))
    ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.32" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.32" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.32" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.49" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.1" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.49" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.32" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.49" 0)) ((:) (Clause ((:) (Atom
    "Setoid.Seq_refl.u0" 0) ([])) (Atom "Coq.setoid_ring.InitialRing.49" 0))
    ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.49" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.49" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.49" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.70" 0)) ((:) (Clause ((:) (Atom
    "Setoid.Seq_refl.u0" 0) ([])) (Atom "Coq.setoid_ring.InitialRing.70" 0))
    ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.70" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.70" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.70" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0)
    ([])) (Atom "Coq.setoid_ring.InitialRing.71" 0)) ((:) (Clause ((:) (Atom
    "prod.u1" 0) ([])) (Atom "Coq.setoid_ring.InitialRing.71" 0)) ((:)
    (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.setoid_ring.InitialRing.71" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.1" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.default_relation.u0" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.equivalence_default.u0" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.1" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.70" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.OrderedRing.1" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.micromega.OrderedRing.21"
    0)) ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_polynom.1" 0) ([]))
    (Atom "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.micromega.OrderedRing.21" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.Tlist.u0" 0) ([])) (Atom
    "RelationClasses.unary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.arrows.u0" 0) ([])) (Atom
    "RelationClasses.unary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "RelationClasses.ternary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "RelationClasses.unary_predicate.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "RelationClasses.pointwise_extension.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "RelationClasses.subrelation_partial_order_obligation_1.u0" 0)) ((:)
    (Clause ((:) (Atom "SetoidTactics.default_relation.u0" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.equivalence_default.u0" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.1" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.70" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.OrderedRing.1" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.OrderedRing.21" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.micromega.RingMicromega.1" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.micromega.RingMicromega.1"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.Env.1" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.EnvRing.9" 0) ([])) (Atom "Coq.micromega.RingMicromega.1"
    0)) ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_polynom.1" 0) ([]))
    (Atom "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.EnvRing.11" 0) ([])) (Atom "Coq.micromega.RingMicromega.3"
    0)) ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.97" 0) ([]))
    (Atom "Coq.micromega.RingMicromega.3" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "RingMicromega.map_option.u0" 0)) ((:) (Clause
    ((:) (Atom "option.u0" 0) ([])) (Atom "RingMicromega.map_option.u1" 0))
    ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom
    "RingMicromega.map_option2.u0" 0)) ((:) (Clause ((:) (Atom "option.u0" 0)
    ([])) (Atom "RingMicromega.map_option2.u1" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "RingMicromega.map_option2.u2" 0)) ((:)
    (Clause ((:) (Atom "EnvRing.PExpr.u0" 0) ([])) (Atom
    "RingMicromega.Formula.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.381" 0) ([])) (Atom "RingMicromega.cnf_of_list.u0" 0))
    ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "RingMicromega.cnf_of_list.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "RingMicromega.cnf_of_list.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "RingMicromega.cnf_of_list.u0"
    0)) ((:) (Clause ((:) (Atom "RingMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "RingMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.381" 0) ([])) (Atom
    "RingMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "prod.u1" 0) ([])) (Atom "RingMicromega.cnf_of_list_correct.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "RingMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj.u0" 0) ([])) (Atom "RingMicromega.cnf_of_list_correct.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.52" 0) ([])) (Atom
    "RingMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "RingMicromega.cnf_normalise.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "RingMicromega.cnf_normalise.u0"
    0)) ((:) (Clause ((:) (Atom "RingMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "RingMicromega.cnf_negate.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "RingMicromega.cnf_negate.u0" 0))
    ((:) (Clause ((:) (Atom "RingMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "RingMicromega.cnf_normalise_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_of_list_correct.u0" 0) ([])) (Atom
    "RingMicromega.cnf_normalise_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_normalise.u0" 0) ([])) (Atom
    "RingMicromega.cnf_normalise_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom
    "RingMicromega.cnf_normalise_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "RingMicromega.cnf_negate_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_of_list_correct.u0" 0) ([])) (Atom
    "RingMicromega.cnf_negate_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.cnf_negate.u0" 0) ([])) (Atom
    "RingMicromega.cnf_negate_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom
    "RingMicromega.cnf_negate_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.Formula.u0" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.98" 0)) ((:) (Clause ((:) (Atom
    "EnvRing.PExpr.u0" 0) ([])) (Atom "Coq.micromega.RingMicromega.98" 0))
    ((:) (Clause ((:) (Atom "Coq.micromega.EnvRing.10" 0) ([])) (Atom
    "Coq.micromega.RingMicromega.98" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Structures.OrdersFacts.34" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.ex_iff_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "ex.u0" 0) ([])) (Atom
    "Morphisms_Prop.ex_iff_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.ex_impl_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "ex.u0" 0) ([])) (Atom
    "Morphisms_Prop.ex_impl_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.ex_flip_impl_morphism_obligation_1.u0" 0)) ((:) (Clause
    ((:) (Atom "ex.u0" 0) ([])) (Atom
    "Morphisms_Prop.ex_flip_impl_morphism_obligation_1.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.all_iff_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "all.u0" 0) ([])) (Atom
    "Morphisms_Prop.all_iff_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.all_impl_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "all.u0" 0) ([])) (Atom
    "Morphisms_Prop.all_impl_morphism_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.all_flip_impl_morphism_obligation_1.u0" 0)) ((:) (Clause
    ((:) (Atom "all.u0" 0) ([])) (Atom
    "Morphisms_Prop.all_flip_impl_morphism_obligation_1.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.Acc_pt_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Wf.1" 0) ([])) (Atom "Morphisms_Prop.Acc_pt_morphism.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Morphisms_Prop.Acc_pt_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff.u0" 0) ([])) (Atom
    "Morphisms_Prop.Acc_pt_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.Acc_rel_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Wf.1" 0) ([])) (Atom "Morphisms_Prop.Acc_rel_morphism.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Morphisms_Prop.Acc_rel_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Morphisms_Prop.Acc_rel_morphism.u0"
    0)) ((:) (Clause ((:) (Atom "Morphisms.proper_sym_impl_iff_2.u1" 0) ([]))
    (Atom "Morphisms_Prop.Acc_rel_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms_Prop.well_founded_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.all_iff_morphism_obligation_1.u0" 0) ([])) (Atom
    "Morphisms_Prop.well_founded_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.Acc_rel_morphism.u0" 0) ([])) (Atom
    "Morphisms_Prop.well_founded_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Wf.1" 0) ([])) (Atom "Morphisms_Prop.well_founded_morphism.u0"
    0)) ((:) (Clause ((:) (Atom "all.u0" 0) ([])) (Atom
    "Morphisms_Prop.well_founded_morphism.u0" 0)) ((:) (Clause ((:) (Atom
    "DeclConstant.DeclaredConstant.u0" 0) ([])) (Atom "DeclConstant.GT_O.u0"
    0)) ((:) (Clause ((:) (Atom "DeclConstant.GT.u0" 0) ([])) (Atom
    "DeclConstant.GT_O.u0" 0)) ((:) (Clause ((:) (Atom
    "DeclConstant.DeclaredConstant.u0" 0) ([])) (Atom
    "DeclConstant.GT_APP1.u0" 0)) ((:) (Clause ((:) (Atom
    "DeclConstant.GT.u0" 0) ([])) (Atom "DeclConstant.GT_APP1.u0" 0)) ((:)
    (Clause ((:) (Atom "DeclConstant.DeclaredConstant.u0" 0) ([])) (Atom
    "DeclConstant.GT_APP1.u1" 0)) ((:) (Clause ((:) (Atom
    "DeclConstant.GT.u0" 0) ([])) (Atom "DeclConstant.GT_APP1.u1" 0)) ((:)
    (Clause ((:) (Atom "DeclConstant.DeclaredConstant.u0" 0) ([])) (Atom
    "DeclConstant.GT_APP2.u0" 0)) ((:) (Clause ((:) (Atom
    "DeclConstant.GT.u0" 0) ([])) (Atom "DeclConstant.GT_APP2.u0" 0)) ((:)
    (Clause ((:) (Atom "DeclConstant.DeclaredConstant.u0" 0) ([])) (Atom
    "DeclConstant.GT_APP2.u1" 0)) ((:) (Clause ((:) (Atom
    "DeclConstant.GT.u0" 0) ([])) (Atom "DeclConstant.GT_APP2.u1" 0)) ((:)
    (Clause ((:) (Atom "DeclConstant.DeclaredConstant.u0" 0) ([])) (Atom
    "DeclConstant.GT_APP2.u2" 0)) ((:) (Clause ((:) (Atom
    "DeclConstant.GT.u0" 0) ([])) (Atom "DeclConstant.GT_APP2.u2" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Wf.2" 0) ([])) (Atom
    "well_founded_induction_type.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Init.Wf.4" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Wf.1"
    0) ([])) (Atom "Coq.Init.Wf.5" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0)
    ([])) (Atom "Coq.Init.Wf.5" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0)
    ([])) (Atom "Coq.Init.Wf.5" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Wf.1"
    0) ([])) (Atom "Coq.Init.Wf.7" 0)) ((:) (Clause ((:) (Atom "total_map.u0"
    0) ([])) (Atom "t_empty.u0" 0)) ((:) (Clause ((:) (Atom "total_map.u0" 0)
    ([])) (Atom "t_update.u0" 0)) ((:) (Clause ((:) (Atom "t_empty.u0" 0)
    ([])) (Atom "t_apply_empty.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "t_apply_empty.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "t_apply_empty.u0" 0)) ((:) (Clause ((:) (Atom
    "total_map.u0" 0) ([])) (Atom "t_update_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "t_update.u0" 0) ([])) (Atom "t_update_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "t_update_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "t_update_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "total_map.u0" 0) ([])) (Atom "t_update_neq.u0" 0)) ((:) (Clause ((:)
    (Atom "t_update.u0" 0) ([])) (Atom "t_update_neq.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "t_update_neq.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_ind_r.u0" 0) ([])) (Atom "t_update_neq.u0" 0)) ((:) (Clause
    ((:) (Atom "total_map.u0" 0) ([])) (Atom "t_update_shadow.u0" 0)) ((:)
    (Clause ((:) (Atom "t_update.u0" 0) ([])) (Atom "t_update_shadow.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "t_update_shadow.u0" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "t_update_shadow.u0"
    0)) ((:) (Clause ((:) (Atom "total_map.u0" 0) ([])) (Atom
    "t_update_same.u0" 0)) ((:) (Clause ((:) (Atom "t_update.u0" 0) ([]))
    (Atom "t_update_same.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "t_update_same.u0" 0)) ((:) (Clause ((:) (Atom "total_map.u0" 0)
    ([])) (Atom "t_update_permute.u0" 0)) ((:) (Clause ((:) (Atom
    "t_update.u0" 0) ([])) (Atom "t_update_permute.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "t_update_permute.u0" 0)) ((:) (Clause ((:)
    (Atom "total_map.u0" 0) ([])) (Atom "partial_map.u0" 0)) ((:) (Clause
    ((:) (Atom "option.u0" 0) ([])) (Atom "partial_map.u0" 0)) ((:) (Clause
    ((:) (Atom "t_empty.u0" 0) ([])) (Atom "empty.u0" 0)) ((:) (Clause ((:)
    (Atom "partial_map.u0" 0) ([])) (Atom "empty.u0" 0)) ((:) (Clause ((:)
    (Atom "option.u0" 0) ([])) (Atom "empty.u0" 0)) ((:) (Clause ((:) (Atom
    "t_update.u0" 0) ([])) (Atom "update.u0" 0)) ((:) (Clause ((:) (Atom
    "partial_map.u0" 0) ([])) (Atom "update.u0" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "update.u0" 0)) ((:) (Clause ((:) (Atom
    "t_apply_empty.u0" 0) ([])) (Atom "apply_empty.u0" 0)) ((:) (Clause ((:)
    (Atom "empty.u0" 0) ([])) (Atom "apply_empty.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "apply_empty.u0" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "apply_empty.u0" 0)) ((:) (Clause ((:) (Atom
    "t_update_eq.u0" 0) ([])) (Atom "update_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "partial_map.u0" 0) ([])) (Atom "update_eq.u0" 0)) ((:) (Clause
    ((:) (Atom "update.u0" 0) ([])) (Atom "update_eq.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "update_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_ind_r.u0" 0) ([])) (Atom "update_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "option.u0" 0) ([])) (Atom "update_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "t_update_neq.u0" 0) ([])) (Atom "update_neq.u0" 0)) ((:) (Clause
    ((:) (Atom "partial_map.u0" 0) ([])) (Atom "update_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "update.u0" 0) ([])) (Atom "update_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "update_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "update_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "update_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "t_update.u0" 0) ([])) (Atom "update_shadow.u0" 0))
    ((:) (Clause ((:) (Atom "t_update_shadow.u0" 0) ([])) (Atom
    "update_shadow.u0" 0)) ((:) (Clause ((:) (Atom "partial_map.u0" 0) ([]))
    (Atom "update_shadow.u0" 0)) ((:) (Clause ((:) (Atom "update.u0" 0) ([]))
    (Atom "update_shadow.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "update_shadow.u0" 0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([]))
    (Atom "update_shadow.u0" 0)) ((:) (Clause ((:) (Atom "t_update.u0" 0)
    ([])) (Atom "update_same.u0" 0)) ((:) (Clause ((:) (Atom
    "t_update_same.u0" 0) ([])) (Atom "update_same.u0" 0)) ((:) (Clause ((:)
    (Atom "partial_map.u0" 0) ([])) (Atom "update_same.u0" 0)) ((:) (Clause
    ((:) (Atom "update.u0" 0) ([])) (Atom "update_same.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "update_same.u0" 0)) ((:) (Clause ((:)
    (Atom "option.u0" 0) ([])) (Atom "update_same.u0" 0)) ((:) (Clause ((:)
    (Atom "t_update_permute.u0" 0) ([])) (Atom "update_permute.u0" 0)) ((:)
    (Clause ((:) (Atom "partial_map.u0" 0) ([])) (Atom "update_permute.u0"
    0)) ((:) (Clause ((:) (Atom "update.u0" 0) ([])) (Atom
    "update_permute.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "update_permute.u0" 0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([]))
    (Atom "update_permute.u0" 0)) ((:) (Clause ((:) (Atom "partial_map.u0" 0)
    ([])) (Atom "inclusion.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "inclusion.u0" 0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([]))
    (Atom "inclusion.u0" 0)) ((:) (Clause ((:) (Atom "partial_map.u0" 0)
    ([])) (Atom "inclusion_update.u0" 0)) ((:) (Clause ((:) (Atom "update.u0"
    0) ([])) (Atom "inclusion_update.u0" 0)) ((:) (Clause ((:) (Atom
    "update_eq.u0" 0) ([])) (Atom "inclusion_update.u0" 0)) ((:) (Clause ((:)
    (Atom "update_neq.u0" 0) ([])) (Atom "inclusion_update.u0" 0)) ((:)
    (Clause ((:) (Atom "inclusion.u0" 0) ([])) (Atom "inclusion_update.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "inclusion_update.u0"
    0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom
    "inclusion_update.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.11"
    0) ([])) (Atom "iter.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "if_negb.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "andb_if.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "negb_if.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Coq.Lists.List.1" 0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom
    "Coq.Lists.List.1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.Lists.List.1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0)
    ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom
    "app_nil_r.u0" 0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:)
    (Atom "app_nil_r.u1" 0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause
    ((:) (Atom "app_assoc.u0" 0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:)
    (Clause ((:) (Atom "app_assoc.u1" 0) ([])) (Atom "Coq.Lists.List.13" 0))
    ((:) (Clause ((:) (Atom "app_eq_app.u0" 0) ([])) (Atom
    "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "sig.u0"
    0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "sigT.u0"
    0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "sigT.u1"
    0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom "sumor.u0"
    0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Datatypes.61" 0) ([])) (Atom "Coq.Lists.List.13" 0)) ((:)
    (Clause ((:) (Atom "length.u0" 0) ([])) (Atom "Coq.Lists.List.13" 0))
    ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.13" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "app_eq_app.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "app_eq_app.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "app_eq_app.u0" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "app_eq_app.u0" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "app_eq_app.u0" 0)) ((:)
    (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "app_eq_app.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0)
    ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.13" 0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause
    ((:) (Atom "nth_split.u0" 0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:)
    (Clause ((:) (Atom "nth_ext.u0" 0) ([])) (Atom "Coq.Lists.List.44" 0))
    ((:) (Clause ((:) (Atom "nth_error_split.u0" 0) ([])) (Atom
    "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom "remove_app.u0" 0) ([]))
    (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom "notin_remove.u0"
    0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0)
    ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:)
    (Clause ((:) (Atom "eq_rect_r.u0" 0) ([])) (Atom "Coq.Lists.List.44" 0))
    ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([])) (Atom "Coq.Lists.List.44"
    0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "Coq.Lists.List.44"
    0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "Coq.Lists.List.44"
    0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "Coq.Lists.List.44"
    0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom
    "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.61"
    0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:) (Atom
    "length.u0" 0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:)
    (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.44" 0)) ((:) (Clause ((:)
    (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.Lists.List.44" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom
    "Coq.Lists.List.247" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.13" 0)
    ([])) (Atom "Coq.Lists.List.247" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.247" 0)) ((:) (Clause
    ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.Lists.List.247" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.247" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.247" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.247"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.247"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.61" 0) ([])) (Atom
    "Coq.Lists.List.247" 0)) ((:) (Clause ((:) (Atom "length.u0" 0) ([]))
    (Atom "Coq.Lists.List.247" 0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([]))
    (Atom "Coq.Lists.List.247" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1"
    0) ([])) (Atom "Coq.Lists.List.277" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.277" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom "Coq.Lists.List.277" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.Lists.List.277" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.277" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.277"
    0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom
    "Coq.Lists.List.277" 0)) ((:) (Clause ((:) (Atom "option_map.u0" 0) ([]))
    (Atom "Coq.Lists.List.277" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Coq.Lists.List.277" 0)) ((:) (Clause ((:) (Atom "length.u0" 0)
    ([])) (Atom "Coq.Lists.List.277" 0)) ((:) (Clause ((:) (Atom "app.u0" 0)
    ([])) (Atom "Coq.Lists.List.277" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "Coq.Lists.List.278" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.13" 0) ([])) (Atom "Coq.Lists.List.278" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.44" 0) ([])) (Atom
    "Coq.Lists.List.278" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0)
    ([])) (Atom "Coq.Lists.List.278" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.278" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.278" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.278" 0)) ((:)
    (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "Coq.Lists.List.278" 0))
    ((:) (Clause ((:) (Atom "option_map.u1" 0) ([])) (Atom
    "Coq.Lists.List.278" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.Lists.List.278" 0)) ((:) (Clause ((:) (Atom "length.u0" 0) ([]))
    (Atom "Coq.Lists.List.278" 0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([]))
    (Atom "Coq.Lists.List.278" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1"
    0) ([])) (Atom "Coq.Lists.List.318" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.277" 0) ([])) (Atom "Coq.Lists.List.318" 0)) ((:) (Clause
    ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.Lists.List.318" 0)) ((:) (Clause
    ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.318" 0)) ((:) (Clause
    ((:) (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.318" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom "Coq.Lists.List.319" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Coq.Lists.List.319" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0)
    ([])) (Atom "Coq.Lists.List.319" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0)
    ([])) (Atom "Coq.Lists.List.319" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.319" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.319" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.319" 0)) ((:) (Clause ((:)
    (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.319" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.247" 0) ([])) (Atom "concat_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "concat_map.u0"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "concat_map.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "concat_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([]))
    (Atom "concat_map.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "concat_map.u1" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "concat_map.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "concat_map.u1" 0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom
    "concat_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.44" 0) ([]))
    (Atom "remove_concat.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247"
    0) ([])) (Atom "remove_concat.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.318" 0) ([])) (Atom "remove_concat.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.319" 0) ([])) (Atom "remove_concat.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "remove_concat.u0" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "remove_concat.u0"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "remove_concat.u0"
    0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "remove_concat.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "map_id.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([]))
    (Atom "map_id.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "map_id.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "map_id.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "map_id.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([]))
    (Atom "map_map.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "map_map.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([]))
    (Atom "map_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0)
    ([])) (Atom "map_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278"
    0) ([])) (Atom "map_map.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "map_map.u2" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "map_map.u2" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "map_map.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([]))
    (Atom "map_ext_in.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0)
    ([])) (Atom "map_ext_in.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "map_ext_in.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "map_ext_in.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0)
    ([])) (Atom "map_ext_in.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "map_ext_in.u1" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "map_ext_in.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "map_ext_in.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0)
    ([])) (Atom "ext_in_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.277" 0) ([])) (Atom "ext_in_map.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_ind_r.u0" 0) ([])) (Atom "ext_in_map.u0" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "ext_in_map.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.278" 0) ([])) (Atom "ext_in_map.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "ext_in_map.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "ext_in_map.u1" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "ext_in_map.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom "map_ext_in_iff.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "map_ext_in_iff.u0" 0)) ((:) (Clause ((:) (Atom "map_ext_in.u0" 0) ([]))
    (Atom "map_ext_in_iff.u0" 0)) ((:) (Clause ((:) (Atom "ext_in_map.u0" 0)
    ([])) (Atom "map_ext_in_iff.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "map_ext_in_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "map_ext_in_iff.u1" 0)) ((:) (Clause
    ((:) (Atom "map_ext_in.u1" 0) ([])) (Atom "map_ext_in_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "ext_in_map.u1" 0) ([])) (Atom "map_ext_in_iff.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "map_ext_in_iff.u1" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "map_ext_in_iff.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "map_ext.u0"
    0)) ((:) (Clause ((:) (Atom "map_ext_in.u0" 0) ([])) (Atom "map_ext.u0"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "map_ext.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom "map_ext.u1"
    0)) ((:) (Clause ((:) (Atom "map_ext_in.u1" 0) ([])) (Atom "map_ext.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "map_ext.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "map_ext.u1" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "map_ext.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "flat_map_ext.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.318" 0) ([])) (Atom "flat_map_ext.u0"
    0)) ((:) (Clause ((:) (Atom "map_ext.u0" 0) ([])) (Atom "flat_map_ext.u0"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "flat_map_ext.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "flat_map_ext.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0)
    ([])) (Atom "flat_map_ext.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.319" 0) ([])) (Atom "flat_map_ext.u1" 0)) ((:) (Clause
    ((:) (Atom "map_ext.u1" 0) ([])) (Atom "flat_map_ext.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "flat_map_ext.u1" 0)) ((:) (Clause ((:)
    (Atom "eq_ind_r.u0" 0) ([])) (Atom "flat_map_ext.u1" 0)) ((:) (Clause
    ((:) (Atom "list.u0" 0) ([])) (Atom "flat_map_ext.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.44" 0) ([])) (Atom "nth_nth_nth_map.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom
    "nth_nth_nth_map.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "nth_nth_nth_map.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "nth_nth_nth_map.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "nth_nth_nth_map.u0" 0)) ((:) (Clause ((:) (Atom "length.u0" 0)
    ([])) (Atom "nth_nth_nth_map.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.377" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.377" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.378" 0)) ((:) (Clause ((:)
    (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.378" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.13" 0) ([])) (Atom "fold_left_length.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "fold_left_length.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.378" 0)
    ([])) (Atom "fold_left_length.u0" 0)) ((:) (Clause ((:) (Atom "list.u0"
    0) ([])) (Atom "fold_left_length.u0" 0)) ((:) (Clause ((:) (Atom
    "length.u0" 0) ([])) (Atom "fold_left_length.u0" 0)) ((:) (Clause ((:)
    (Atom "app.u0" 0) ([])) (Atom "fold_left_length.u0" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.382" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.382" 0) ([])) (Atom "fold_right_app.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "fold_right_app.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "fold_right_app.u0" 0)) ((:)
    (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "fold_right_app.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.381" 0) ([])) (Atom
    "fold_right_app.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "fold_right_app.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "fold_right_app.u1" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "fold_right_app.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.247" 0) ([])) (Atom "fold_left_rev_right.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.378" 0) ([])) (Atom
    "fold_left_rev_right.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.382"
    0) ([])) (Atom "fold_left_rev_right.u0" 0)) ((:) (Clause ((:) (Atom
    "fold_right_app.u0" 0) ([])) (Atom "fold_left_rev_right.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "fold_left_rev_right.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.377" 0) ([])) (Atom
    "fold_left_rev_right.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.381"
    0) ([])) (Atom "fold_left_rev_right.u1" 0)) ((:) (Clause ((:) (Atom
    "fold_right_app.u1" 0) ([])) (Atom "fold_left_rev_right.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "fold_left_rev_right.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.377" 0) ([])) (Atom
    "fold_symmetric.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.378" 0)
    ([])) (Atom "fold_symmetric.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.381" 0) ([])) (Atom "fold_symmetric.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.382" 0) ([])) (Atom "fold_symmetric.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "fold_symmetric.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "fold_symmetric.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "fold_symmetric.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "fold_symmetric.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "list_power.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.318" 0) ([])) (Atom "list_power.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.319" 0) ([])) (Atom "list_power.u0"
    0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom "list_power.u0" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "list_power.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "list_power.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom
    "list_power.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.318" 0) ([]))
    (Atom "list_power.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.319" 0)
    ([])) (Atom "list_power.u1" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0)
    ([])) (Atom "list_power.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "list_power.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "Coq.Lists.List.400" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.400" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0)
    ([])) (Atom "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "Coq.Lists.List.400" 0)) ((:) (Clause
    ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.Lists.List.400" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.400" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.400" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.400"
    0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom
    "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom "length.u0" 0) ([]))
    (Atom "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([]))
    (Atom "Coq.Lists.List.400" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1"
    0) ([])) (Atom "Coq.Lists.List.454" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.454" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "Coq.Lists.List.454" 0))
    ((:) (Clause ((:) (Atom "map_ext_in_iff.u0" 0) ([])) (Atom
    "Coq.Lists.List.454" 0)) ((:) (Clause ((:) (Atom "map_ext.u0" 0) ([]))
    (Atom "Coq.Lists.List.454" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.400" 0) ([])) (Atom "Coq.Lists.List.454" 0)) ((:) (Clause
    ((:) (Atom "filter_ext_in.u0" 0) ([])) (Atom "Coq.Lists.List.454" 0))
    ((:) (Clause ((:) (Atom "remove_alt.u0" 0) ([])) (Atom
    "Coq.Lists.List.454" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Coq.Lists.List.454" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "Coq.Lists.List.454" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.454" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.454" 0)) ((:) (Clause ((:)
    (Atom "length.u0" 0) ([])) (Atom "Coq.Lists.List.454" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom "Coq.Lists.List.465" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.13" 0) ([])) (Atom
    "Coq.Lists.List.465" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.44" 0)
    ([])) (Atom "Coq.Lists.List.465" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "Coq.Lists.List.465" 0)) ((:) (Clause
    ((:) (Atom "split_combine.u0" 0) ([])) (Atom "Coq.Lists.List.465" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.465" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Lists.List.465" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Coq.Lists.List.465" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([]))
    (Atom "Coq.Lists.List.465" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.26" 0) ([])) (Atom "Coq.Lists.List.465" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.465" 0)) ((:)
    (Clause ((:) (Atom "length.u0" 0) ([])) (Atom "Coq.Lists.List.465" 0))
    ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.465" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom
    "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.13" 0)
    ([])) (Atom "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.466" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "Coq.Lists.List.466" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom
    "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "split_combine.u0" 0)
    ([])) (Atom "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0)
    ([])) (Atom "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.466" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.466" 0)) ((:)
    (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "Coq.Lists.List.466" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Datatypes.27" 0) ([])) (Atom
    "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "length.u0" 0) ([]))
    (Atom "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([]))
    (Atom "Coq.Lists.List.466" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Lists.List.477" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Coq.Lists.List.477" 0)) ((:) (Clause ((:) (Atom "length.u0" 0)
    ([])) (Atom "Coq.Lists.List.477" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "Coq.Lists.List.479" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.13" 0) ([])) (Atom "Coq.Lists.List.479" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.44" 0) ([])) (Atom
    "Coq.Lists.List.479" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.400" 0)
    ([])) (Atom "Coq.Lists.List.479" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.479" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.479" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.479" 0)) ((:) (Clause ((:)
    (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.479" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.1" 0) ([])) (Atom "incl_map.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "incl_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.479" 0) ([])) (Atom "incl_map.u0" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "incl_map.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "incl_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom "incl_map.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom "incl_map.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.479" 0) ([])) (Atom
    "incl_map.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "incl_map.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.13" 0)
    ([])) (Atom "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.495" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom "Coq.Lists.List.495" 0))
    ((:) (Clause ((:) (Atom "firstn_all2.u0" 0) ([])) (Atom
    "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom "firstn_app.u0" 0) ([]))
    (Atom "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom "firstn_firstn.u0"
    0) ([])) (Atom "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom
    "firstn_skipn.u0" 0) ([])) (Atom "Coq.Lists.List.495" 0)) ((:) (Clause
    ((:) (Atom "firstn_skipn_rev.u0" 0) ([])) (Atom "Coq.Lists.List.495" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.495" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom "length.u0" 0)
    ([])) (Atom "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom "app.u0" 0)
    ([])) (Atom "Coq.Lists.List.495" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.Lists.List.495" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "Coq.Lists.List.572" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0)
    ([])) (Atom "Coq.Lists.List.572" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.495" 0) ([])) (Atom "Coq.Lists.List.572" 0)) ((:) (Clause
    ((:) (Atom "firstn_map.u0" 0) ([])) (Atom "Coq.Lists.List.572" 0)) ((:)
    (Clause ((:) (Atom "firstn_map.u1" 0) ([])) (Atom "Coq.Lists.List.572"
    0)) ((:) (Clause ((:) (Atom "firstn_map.u2" 0) ([])) (Atom
    "Coq.Lists.List.572" 0)) ((:) (Clause ((:) (Atom "firstn_map.u3" 0) ([]))
    (Atom "Coq.Lists.List.572" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Lists.List.572" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.572" 0)) ((:) (Clause
    ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.572" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.13" 0) ([])) (Atom "Coq.Lists.List.581" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.465" 0) ([])) (Atom
    "Coq.Lists.List.581" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.466" 0)
    ([])) (Atom "Coq.Lists.List.581" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.495" 0) ([])) (Atom "Coq.Lists.List.581" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.581" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.581" 0)) ((:)
    (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom "Coq.Lists.List.581" 0)) ((:)
    (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "Coq.Lists.List.581" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.581" 0)) ((:)
    (Clause ((:) (Atom "length.u0" 0) ([])) (Atom "Coq.Lists.List.581" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom
    "Coq.Lists.List.582" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.13" 0)
    ([])) (Atom "Coq.Lists.List.582" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.479" 0) ([])) (Atom "Coq.Lists.List.582" 0)) ((:) (Clause
    ((:) (Atom "Add_split.u0" 0) ([])) (Atom "Coq.Lists.List.582" 0)) ((:)
    (Clause ((:) (Atom "Add_split.u1" 0) ([])) (Atom "Coq.Lists.List.582" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.Lists.List.582" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.582" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Lists.List.582" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Coq.Lists.List.582" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Coq.Lists.List.582" 0)) ((:) (Clause ((:) (Atom "length.u0" 0)
    ([])) (Atom "Coq.Lists.List.582" 0)) ((:) (Clause ((:) (Atom "app.u0" 0)
    ([])) (Atom "Coq.Lists.List.582" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.all_iff_morphism_obligation_1.u0" 0) ([])) (Atom
    "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0)
    ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.13" 0) ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.615" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.400" 0)
    ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.479" 0) ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.582" 0) ([])) (Atom "Coq.Lists.List.615" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.Lists.List.615" 0))
    ((:) (Clause ((:) (Atom "all.u0" 0) ([])) (Atom "Coq.Lists.List.615" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Lists.List.615" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom "option.u0" 0)
    ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom "length.u0"
    0) ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom "app.u0"
    0) ([])) (Atom "Coq.Lists.List.615" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.Lists.List.615" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "NoDup_map_inv.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.615" 0) ([])) (Atom
    "NoDup_map_inv.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "NoDup_map_inv.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0)
    ([])) (Atom "NoDup_map_inv.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "NoDup_map_inv.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.615" 0) ([])) (Atom "NoDup_map_inv.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "NoDup_map_inv.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "NoDup_map_inv.u1" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "NoDup_map_inv.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "NoDup_map_inv.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1"
    0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.13" 0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.702" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Coq.Lists.List.702" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0)
    ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause ((:) (Atom
    "map_ext_in.u0" 0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.382" 0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.479" 0) ([])) (Atom
    "Coq.Lists.List.702" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "Coq.Lists.List.702" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Coq.Lists.List.702" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause ((:)
    (Atom "length.u0" 0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause
    ((:) (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.702" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Datatypes.61" 0) ([])) (Atom "Forall_rect.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom
    "map_ext_Forall.u0" 0)) ((:) (Clause ((:) (Atom "map_ext_in.u1" 0) ([]))
    (Atom "map_ext_Forall.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "map_ext_Forall.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "map_ext_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.277" 0) ([])) (Atom "Exists_map.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Lists.List.702" 0) ([])) (Atom "Exists_map.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Exists_map.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Exists_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom "Exists_map.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom
    "Exists_map.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Exists_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([]))
    (Atom "Exists_concat.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.702"
    0) ([])) (Atom "Exists_concat.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Exists_concat.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Exists_concat.u0" 0)) ((:) (Clause ((:) (Atom "app.u0" 0)
    ([])) (Atom "Exists_concat.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.277" 0) ([])) (Atom "Exists_flat_map.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.318" 0) ([])) (Atom "Exists_flat_map.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom
    "Exists_flat_map.u0" 0)) ((:) (Clause ((:) (Atom "Exists_map.u0" 0) ([]))
    (Atom "Exists_flat_map.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Exists_flat_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.247" 0) ([])) (Atom "Exists_flat_map.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom "Exists_flat_map.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.319" 0) ([])) (Atom
    "Exists_flat_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0)
    ([])) (Atom "Exists_flat_map.u1" 0)) ((:) (Clause ((:) (Atom
    "Exists_map.u1" 0) ([])) (Atom "Exists_flat_map.u1" 0)) ((:) (Clause ((:)
    (Atom "Exists_concat.u0" 0) ([])) (Atom "Exists_flat_map.u1" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Exists_flat_map.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom "Forall_map.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom
    "Forall_map.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Forall_map.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([]))
    (Atom "Forall_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0)
    ([])) (Atom "Forall_map.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Forall_map.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.247" 0) ([])) (Atom "Forall_concat.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom "Forall_concat.u0" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Forall_concat.u0" 0))
    ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "Forall_concat.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "Forall_flat_map.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.318" 0)
    ([])) (Atom "Forall_flat_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.702" 0) ([])) (Atom "Forall_flat_map.u0" 0)) ((:) (Clause
    ((:) (Atom "Forall_map.u0" 0) ([])) (Atom "Forall_flat_map.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Forall_flat_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Forall_flat_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0)
    ([])) (Atom "Forall_flat_map.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.319" 0) ([])) (Atom "Forall_flat_map.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom "Forall_flat_map.u1" 0))
    ((:) (Clause ((:) (Atom "Forall_map.u1" 0) ([])) (Atom
    "Forall_flat_map.u1" 0)) ((:) (Clause ((:) (Atom "Forall_concat.u0" 0)
    ([])) (Atom "Forall_flat_map.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Forall_flat_map.u1" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0)
    ([])) (Atom "exists_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.702" 0) ([])) (Atom "exists_Forall.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "exists_Forall.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "exists_Forall.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "exists_Forall.u1" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "exists_Forall.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "Forall_image.u0" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "Forall_image.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Forall_image.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0)
    ([])) (Atom "Forall_image.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.702" 0) ([])) (Atom "Forall_image.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Forall_image.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "Forall_image.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Forall_image.u1" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Forall_image.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.13" 0) ([])) (Atom
    "concat_nil_Forall.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247"
    0) ([])) (Atom "concat_nil_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.702" 0) ([])) (Atom "concat_nil_Forall.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "concat_nil_Forall.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "concat_nil_Forall.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "concat_nil_Forall.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "concat_nil_Forall.u0" 0)) ((:) (Clause ((:) (Atom "app.u0"
    0) ([])) (Atom "concat_nil_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "in_flat_map_Exists.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.318" 0) ([])) (Atom
    "in_flat_map_Exists.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.702"
    0) ([])) (Atom "in_flat_map_Exists.u0" 0)) ((:) (Clause ((:) (Atom
    "ex.u0" 0) ([])) (Atom "in_flat_map_Exists.u0" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "in_flat_map_Exists.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom "in_flat_map_Exists.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.319" 0) ([])) (Atom
    "in_flat_map_Exists.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "in_flat_map_Exists.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.318" 0) ([])) (Atom "notin_flat_map_Forall.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom
    "notin_flat_map_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "in_flat_map_Exists.u0" 0) ([])) (Atom "notin_flat_map_Forall.u0" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "notin_flat_map_Forall.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1"
    0) ([])) (Atom "notin_flat_map_Forall.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.319" 0) ([])) (Atom "notin_flat_map_Forall.u1" 0)) ((:)
    (Clause ((:) (Atom "in_flat_map_Exists.u1" 0) ([])) (Atom
    "notin_flat_map_Forall.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "notin_flat_map_Forall.u1" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0)
    ([])) (Atom "Coq.Lists.List.821" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.821" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.821" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.821" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.821" 0)) ((:)
    (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.821" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom "Coq.Lists.List.838"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom
    "Coq.Lists.List.838" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Coq.Lists.List.838" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Coq.Lists.List.838" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Coq.Lists.List.838" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Lists.List.857" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0)
    ([])) (Atom "Coq.Lists.List.857" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.44" 0) ([])) (Atom "Coq.Lists.List.857" 0)) ((:) (Clause
    ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom "Coq.Lists.List.857" 0))
    ((:) (Clause ((:) (Atom "repeat_cons.u0" 0) ([])) (Atom
    "Coq.Lists.List.857" 0)) ((:) (Clause ((:) (Atom "count_occ_unique.u0" 0)
    ([])) (Atom "Coq.Lists.List.857" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Lists.List.857" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Lists.List.857" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Lists.List.857" 0)) ((:)
    (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "Coq.Lists.List.857" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.Lists.List.857" 0))
    ((:) (Clause ((:) (Atom "length.u0" 0) ([])) (Atom "Coq.Lists.List.857"
    0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "Coq.Lists.List.857"
    0)) ((:) (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.Lists.List.857" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0)
    ([])) (Atom "repeat_to_concat.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.857" 0) ([])) (Atom "repeat_to_concat.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "repeat_to_concat.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "repeat_to_concat.u0" 0)) ((:) (Clause ((:) (Atom "all.u0" 0) ([]))
    (Atom "Coq.Init.Logic.7" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Init.Logic.10" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sind_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_sind_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_ind_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_ind_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_rec_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_rec_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_rect_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_rect_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9"
    0) ([])) (Atom "eq_rect_r.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Init.Logic.16" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Init.Logic.17" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "Coq.Init.Logic.17" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "f_equal_dep2.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "f_equal_dep2.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "f_equal_dep2.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "f_equal_dep2.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "f_equal_dep2.u2" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "f_equal_dep2.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal_dep2.u3" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "f_equal_dep2.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "rew_opp_r.u0" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u0" 0) ([]))
    (Atom "rew_opp_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_opp_r.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "rew_opp_r.u1" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([]))
    (Atom "rew_opp_r.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_opp_l.u0" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u0" 0) ([])) (Atom
    "rew_opp_l.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_opp_l.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "rew_opp_l.u1" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([]))
    (Atom "rew_opp_l.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal2.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal2.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal2.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal3.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal3.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal3.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal3.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal4.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal4.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal4.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal4.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal4.u4" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal5.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal5.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal5.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal5.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal5.u4" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal5.u5" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "f_equal_compose.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "f_equal_compose.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "f_equal_compose.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "f_equal_compose.u2" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "f_equal_compose.u2" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_trans_refl_l.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_trans_refl_l.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_trans_refl_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_trans_refl_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "eq_sym_involutive.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_sym_involutive.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_trans_sym_inv_l.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_trans_sym_inv_l.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_trans_sym_inv_r.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_trans_sym_inv_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_trans_assoc.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "eq_trans_assoc.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "rew_map.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_map.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "rew_map.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_map.u2" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "rew_map.u2" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_trans_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "eq_trans_map.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_trans_map.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_trans_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_trans_map.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "map_subst.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9"
    0) ([])) (Atom "map_subst.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "map_subst.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9"
    0) ([])) (Atom "map_subst.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "map_subst_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "map_subst_map.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "map_subst_map.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "map_subst_map.u2" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "map_subst_map.u2"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "map_subst_map.u3" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "map_subst_map.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_swap.u0" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u0" 0) ([])) (Atom
    "rew_swap.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_swap.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "rew_swap.u1" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([]))
    (Atom "rew_swap.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_compose.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([]))
    (Atom "rew_compose.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_compose.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "rew_compose.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_id_comm_l.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_id_comm_l.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_trans_sym_inv_l.u0" 0) ([])) (Atom "eq_id_comm_l.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_id_comm_r.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "eq_id_comm_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_trans_refl_l.u0" 0) ([])) (Atom "eq_id_comm_r.u0"
    0)) ((:) (Clause ((:) (Atom "eq_trans_sym_inv_l.u0" 0) ([])) (Atom
    "eq_id_comm_r.u0" 0)) ((:) (Clause ((:) (Atom "eq_id_comm_l.u0" 0) ([]))
    (Atom "eq_id_comm_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_refl_map_distr.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_refl_map_distr.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_refl_map_distr.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_refl_map_distr.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_trans_map_distr.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10"
    0) ([])) (Atom "eq_trans_map_distr.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "eq_trans_map_distr.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "eq_trans_map_distr.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sym_map_distr.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_sym_map_distr.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sym_map_distr.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_sym_map_distr.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "eq_trans_sym_distr.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_trans_sym_distr.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_trans_rew_distr.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_trans_rew_distr.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_trans_rew_distr.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_trans_rew_distr.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_const.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_const.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "rew_const.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "unique.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "uniqueness.u0" 0)) ((:) (Clause ((:) (Atom
    "ex.u0" 0) ([])) (Atom "unique_existence.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "unique_existence.u0" 0)) ((:) (Clause
    ((:) (Atom "unique.u0" 0) ([])) (Atom "unique_existence.u0" 0)) ((:)
    (Clause ((:) (Atom "uniqueness.u0" 0) ([])) (Atom "unique_existence.u0"
    0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "forall_exists_unique_domain_coincide.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "forall_exists_unique_domain_coincide.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "forall_exists_unique_domain_coincide.u0" 0)) ((:) (Clause ((:) (Atom
    "unique.u0" 0) ([])) (Atom "forall_exists_unique_domain_coincide.u0" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "forall_exists_coincide_unique_domain.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "forall_exists_coincide_unique_domain.u0" 0)) ((:)
    (Clause ((:) (Atom "unique.u0" 0) ([])) (Atom
    "forall_exists_coincide_unique_domain.u0" 0)) ((:) (Clause ((:) (Atom
    "ex.u0" 0) ([])) (Atom "exists_inhabited.u0" 0)) ((:) (Clause ((:) (Atom
    "inhabited.u0" 0) ([])) (Atom "exists_inhabited.u0" 0)) ((:) (Clause ((:)
    (Atom "inhabited.u0" 0) ([])) (Atom "inhabited_covariant.u0" 0)) ((:)
    (Clause ((:) (Atom "inhabited.u0" 0) ([])) (Atom "inhabited_covariant.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_stepl.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_rect_r.u1" 0) ([])) (Atom "ex_rect.u0" 0)) ((:)
    (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "eq_ex_intro_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_ex_intro_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "eq_ex_intro.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_ex_intro.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ex_intro_uncurried.u0" 0) ([])) (Atom
    "eq_ex_intro.u0" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([]))
    (Atom "eq_ex_rect.u0" 0)) ((:) (Clause ((:) (Atom "eq_ex_rect.u0" 0)
    ([])) (Atom "eq_ex_rect_ex_intro_l.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ex_rect.u0" 0) ([])) (Atom "eq_ex_rect_ex_intro_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ex_rect.u0" 0) ([])) (Atom
    "eq_ex_rect_ex_intro.u0" 0)) ((:) (Clause ((:) (Atom "eq_ex_rect.u0" 0)
    ([])) (Atom "eq_ex_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "ex.u0"
    0) ([])) (Atom "eq_ex_intro_hprop.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "eq_ex_intro_hprop.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ex_intro.u0" 0) ([])) (Atom "eq_ex_intro_hprop.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_ex.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_rect_r.u1" 0) ([])) (Atom "ex2_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "ex2.u0" 0) ([])) (Atom "eq_ex_intro2_uncurried.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_ex_intro2_uncurried.u0" 0)) ((:) (Clause
    ((:) (Atom "ex2.u0" 0) ([])) (Atom "eq_ex_intro2.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_ex_intro2.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_ex_intro2_uncurried.u0" 0) ([])) (Atom "eq_ex_intro2.u0" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "eq_ex_intro2_hprop_nondep.u0" 0)) ((:) (Clause ((:) (Atom "ex2.u0" 0)
    ([])) (Atom "eq_ex_intro2_hprop_nondep.u0" 0)) ((:) (Clause ((:) (Atom
    "ex2.u0" 0) ([])) (Atom "eq_ex_intro2_hprop.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_ex_intro2_hprop.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_ex_intro2.u0" 0) ([])) (Atom "eq_ex_intro2_hprop.u0" 0))
    ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([])) (Atom "eq_ex2_rect.u0"
    0)) ((:) (Clause ((:) (Atom "eq_ex2_rect.u0" 0) ([])) (Atom
    "eq_ex2_rect_ex_intro2_l.u0" 0)) ((:) (Clause ((:) (Atom "eq_ex2_rect.u0"
    0) ([])) (Atom "eq_ex2_rect_ex_intro2_r.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ex2_rect.u0" 0) ([])) (Atom "eq_ex2_rect_ex_intro2.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ex2_rect.u0" 0) ([])) (Atom
    "eq_ex2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "rew_ex2.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "nat_rect_succ_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.11"
    0) ([])) (Atom "nat_rect_succ_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "nat_rect_plus.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "nat_rect_plus.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Datatypes.11" 0) ([])) (Atom "nat_rect_plus.u0" 0)) ((:)
    (Clause ((:) (Atom "iter.u0" 0) ([])) (Atom "Nnat.N2Nat.inj_iter.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Nnat.N2Nat.inj_iter.u0"
    0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Nnat.N2Nat.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom
    "Pnat.Pos2Nat.inj_iter.u0" 0) ([])) (Atom "Nnat.N2Nat.inj_iter.u0" 0))
    ((:) (Clause ((:) (Atom "BinNat.N.iter.u0" 0) ([])) (Atom
    "Nnat.N2Nat.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom "iter.u0" 0) ([]))
    (Atom "Nnat.Nat2N.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Nnat.Nat2N.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom
    "Nnat.N2Nat.inj_iter.u0" 0) ([])) (Atom "Nnat.Nat2N.inj_iter.u0" 0)) ((:)
    (Clause ((:) (Atom "BinNat.N.iter.u0" 0) ([])) (Atom
    "Nnat.Nat2N.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Pnat.Pos2Nat.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Pnat.Pos2Nat.inj_iter.u0" 0)) ((:)
    (Clause ((:) (Atom "BinPos.Pos.iter_succ.u0" 0) ([])) (Atom
    "Pnat.Pos2Nat.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter.u0" 0) ([])) (Atom "Pnat.Pos2Nat.inj_iter.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Datatypes.11" 0) ([])) (Atom
    "Pnat.Pos2Nat.inj_iter.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "Coq.Init.Specif.16" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "sig_of_sig2.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([]))
    (Atom "sig_of_sig2.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([]))
    (Atom "Coq.Init.Specif.21" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "Coq.Init.Specif.21" 0)) ((:) (Clause
    ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom "Coq.Init.Specif.21" 0)) ((:)
    (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "Coq.Init.Specif.22" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "Coq.Init.Specif.23" 0)) ((:)
    (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "sigT_of_sigT2.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom "sigT_of_sigT2.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "sigT_of_sigT2.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "sigT_of_sigT2.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "sigT_of_sigT2.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom "Coq.Init.Specif.29" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "Coq.Init.Specif.29" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0)
    ([])) (Atom "Coq.Init.Specif.29" 0)) ((:) (Clause ((:) (Atom "sigT2.u1"
    0) ([])) (Atom "Coq.Init.Specif.30" 0)) ((:) (Clause ((:) (Atom
    "sigT2.u2" 0) ([])) (Atom "Coq.Init.Specif.30" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "Coq.Init.Specif.30" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom "Coq.Init.Specif.30"
    0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom
    "Coq.Init.Specif.30" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "sig_of_sigT.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "sig_of_sigT.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.22" 0)
    ([])) (Atom "sig_of_sigT.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0)
    ([])) (Atom "sigT_of_sig.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0)
    ([])) (Atom "sigT_of_sig.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "sigT_of_sig.u0" 0)) ((:) (Clause
    ((:) (Atom "sig2.u0" 0) ([])) (Atom "sig2_of_sigT2.u0" 0)) ((:) (Clause
    ((:) (Atom "sigT2.u0" 0) ([])) (Atom "sig2_of_sigT2.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "sig2_of_sigT2.u0" 0))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "sig2_of_sigT2.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.29" 0)
    ([])) (Atom "sig2_of_sigT2.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0)
    ([])) (Atom "sigT2_of_sig2.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0)
    ([])) (Atom "sigT2_of_sig2.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "sigT2_of_sig2.u0" 0)) ((:) (Clause
    ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom "sigT2_of_sig2.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.21" 0) ([])) (Atom "sigT2_of_sig2.u0"
    0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "ex_of_sig.u0" 0))
    ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "ex_of_sig.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "ex_of_sig.u0" 0))
    ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "ex_of_sigT.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "ex_of_sigT.u0" 0)) ((:)
    (Clause ((:) (Atom "sig_of_sigT.u0" 0) ([])) (Atom "ex_of_sigT.u0" 0))
    ((:) (Clause ((:) (Atom "ex_of_sig.u0" 0) ([])) (Atom "ex_of_sigT.u0" 0))
    ((:) (Clause ((:) (Atom "ex2.u0" 0) ([])) (Atom "ex2_of_sig2.u0" 0)) ((:)
    (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom "ex2_of_sig2.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "ex2_of_sig2.u0"
    0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "ex2_of_sig2.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.21" 0)
    ([])) (Atom "ex2_of_sig2.u0" 0)) ((:) (Clause ((:) (Atom "ex2.u0" 0)
    ([])) (Atom "ex2_of_sigT2.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0)
    ([])) (Atom "ex2_of_sigT2.u0" 0)) ((:) (Clause ((:) (Atom
    "sig2_of_sigT2.u0" 0) ([])) (Atom "ex2_of_sigT2.u0" 0)) ((:) (Clause ((:)
    (Atom "ex2_of_sig2.u0" 0) ([])) (Atom "ex2_of_sigT2.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "sigT_eta.u0" 0)) ((:) (Clause ((:)
    (Atom "sigT.u0" 0) ([])) (Atom "sigT_eta.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "sigT_eta.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "sigT_eta.u1" 0)) ((:) (Clause ((:) (Atom
    "sigT.u1" 0) ([])) (Atom "sigT_eta.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "sigT_eta.u1" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "sig_eta.u0" 0)) ((:) (Clause ((:) (Atom
    "sig.u0" 0) ([])) (Atom "sig_eta.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "sig_eta.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "sigT2_eta.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT2.u0" 0) ([])) (Atom "sigT2_eta.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "sigT2_eta.u0" 0)) ((:) (Clause ((:)
    (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom "sigT2_eta.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.29" 0) ([])) (Atom "sigT2_eta.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "sigT2_eta.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT2.u1" 0) ([])) (Atom "sigT2_eta.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "sigT2_eta.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom "sigT2_eta.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom "sigT2_eta.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "sigT2_eta.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "sigT2_eta.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom "sigT2_eta.u2" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "sigT2_eta.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "sig2_eta.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "sig2_eta.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([]))
    (Atom "sig2_eta.u0" 0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([]))
    (Atom "sig2_eta.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.21" 0)
    ([])) (Atom "sig2_eta.u0" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([]))
    (Atom "exists_to_inhabited_sig.u0" 0)) ((:) (Clause ((:) (Atom
    "inhabited.u0" 0) ([])) (Atom "exists_to_inhabited_sig.u0" 0)) ((:)
    (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "exists_to_inhabited_sig.u0"
    0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "inhabited_sig_to_exists.u0" 0)) ((:) (Clause ((:) (Atom "inhabited.u0"
    0) ([])) (Atom "inhabited_sig_to_exists.u0" 0)) ((:) (Clause ((:) (Atom
    "sig.u0" 0) ([])) (Atom "inhabited_sig_to_exists.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Init.Specif.78" 0)) ((:) (Clause
    ((:) (Atom "sigT.u0" 0) ([])) (Atom "Coq.Init.Specif.78" 0)) ((:) (Clause
    ((:) (Atom "sigT.u1" 0) ([])) (Atom "Coq.Init.Specif.78" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "Coq.Init.Specif.78" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom
    "Coq.Init.Specif.78" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "Coq.Init.Specif.78" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "Coq.Init.Specif.78" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.26"
    0) ([])) (Atom "Coq.Init.Specif.78" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.27" 0) ([])) (Atom "Coq.Init.Specif.78" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT1_eq.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "projT1_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "projT1_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "projT1_eq.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT1_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "projT1_eq.u1" 0))
    ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "projT1_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "projT1_eq.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "projT2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "projT2_eq.u0" 0))
    ((:) (Clause ((:) (Atom "projT1_eq.u0" 0) ([])) (Atom "projT2_eq.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT2_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "projT2_eq.u1" 0))
    ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "projT2_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "projT2_eq.u1" 0))
    ((:) (Clause ((:) (Atom "projT1_eq.u1" 0) ([])) (Atom "projT2_eq.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "eq_existT_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_existT_uncurried.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "eq_sigT_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "eq_sigT_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_existT_uncurried.u0" 0) ([])) (Atom "eq_sigT_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_sigT_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_existT_uncurried.u1" 0) ([])) (Atom
    "eq_sigT_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_existT_curried.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_existT_curried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_uncurried.u0" 0) ([])) (Atom "eq_existT_curried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_curried.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_existT_curried.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_existT_curried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_uncurried.u1" 0) ([])) (Atom "eq_existT_curried.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_curried_map.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_existT_curried_map.u0" 0)) ((:) (Clause ((:) (Atom "f_equal_dep2.u0"
    0) ([])) (Atom "eq_existT_curried_map.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "eq_existT_curried_map.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "eq_existT_curried_map.u0" 0))
    ((:) (Clause ((:) (Atom "eq_existT_curried.u0" 0) ([])) (Atom
    "eq_existT_curried_map.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT_curried_map.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_existT_curried_map.u1" 0)) ((:)
    (Clause ((:) (Atom "f_equal_dep2.u1" 0) ([])) (Atom
    "eq_existT_curried_map.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_existT_curried_map.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_existT_curried.u0" 0) ([])) (Atom "eq_existT_curried_map.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_curried_map.u2" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_existT_curried_map.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_existT_curried_map.u2" 0)) ((:)
    (Clause ((:) (Atom "f_equal_dep2.u2" 0) ([])) (Atom
    "eq_existT_curried_map.u2" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_existT_curried_map.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_existT_curried_map.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_existT_curried.u1" 0) ([])) (Atom
    "eq_existT_curried_map.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT_curried_map.u3" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_existT_curried_map.u3" 0)) ((:)
    (Clause ((:) (Atom "f_equal_dep2.u3" 0) ([])) (Atom
    "eq_existT_curried_map.u3" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_existT_curried_map.u3" 0)) ((:) (Clause ((:) (Atom
    "eq_existT_curried.u1" 0) ([])) (Atom "eq_existT_curried_map.u3" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_curried_trans.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_existT_curried_trans.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_trans_map.u0" 0) ([])) (Atom "eq_existT_curried_trans.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "eq_existT_curried_trans.u0"
    0)) ((:) (Clause ((:) (Atom "eq_existT_curried.u0" 0) ([])) (Atom
    "eq_existT_curried_trans.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT_curried_trans.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT_curried_trans.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_existT_curried_trans.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_trans_map.u1" 0) ([])) (Atom "eq_existT_curried_trans.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_existT_curried_trans.u1"
    0)) ((:) (Clause ((:) (Atom "eq_existT_curried.u1" 0) ([])) (Atom
    "eq_existT_curried_trans.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT_curried_congr.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0"
    0) ([])) (Atom "eq_existT_curried_congr.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_existT_curried.u0" 0) ([])) (Atom "eq_existT_curried_congr.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_existT_curried_congr.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT_curried_congr.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_existT_curried_congr.u1"
    0)) ((:) (Clause ((:) (Atom "eq_existT_curried.u1" 0) ([])) (Atom
    "eq_existT_curried_congr.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "eq_sigT.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([]))
    (Atom "eq_sigT.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT_uncurried.u0" 0)
    ([])) (Atom "eq_sigT.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0)
    ([])) (Atom "eq_sigT.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_sigT.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.23" 0)
    ([])) (Atom "eq_sigT.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_uncurried.u1" 0) ([])) (Atom "eq_sigT.u1" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_existT_l.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "eq_existT_l.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_existT_l.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_sigT.u0" 0) ([])) (Atom "eq_existT_l.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_l.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT_l.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_existT_l.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "eq_existT_l.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT.u1" 0) ([])) (Atom "eq_existT_l.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_r.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "eq_existT_r.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "eq_existT_r.u0"
    0)) ((:) (Clause ((:) (Atom "eq_sigT.u0" 0) ([])) (Atom "eq_existT_r.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT_r.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_existT_r.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "eq_existT_r.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.23" 0)
    ([])) (Atom "eq_existT_r.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT.u1" 0)
    ([])) (Atom "eq_existT_r.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT_hprop.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_sigT_hprop.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.22"
    0) ([])) (Atom "eq_sigT_hprop.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT.u0" 0) ([])) (Atom "eq_sigT_hprop.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_hprop.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT_hprop.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_sigT_hprop.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_hprop.u1"
    0)) ((:) (Clause ((:) (Atom "eq_sigT.u1" 0) ([])) (Atom
    "eq_sigT_hprop.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "eq_sigT_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "eq_sigT_uncurried_iff.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT_uncurried_iff.u0" 0))
    ((:) (Clause ((:) (Atom "eq_sigT_uncurried.u0" 0) ([])) (Atom
    "eq_sigT_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT_uncurried_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "eq_sigT_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_sigT_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_uncurried_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT_uncurried.u1" 0) ([])) (Atom
    "eq_sigT_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT_rect.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_sigT_rect.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.22"
    0) ([])) (Atom "eq_sigT_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "projT1_eq.u0" 0) ([])) (Atom "eq_sigT_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "projT2_eq.u0" 0) ([])) (Atom "eq_sigT_rect.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_sigT.u0" 0) ([])) (Atom "eq_sigT_rect.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_rect.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT_rect.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_sigT_rect.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_rect.u1"
    0)) ((:) (Clause ((:) (Atom "projT1_eq.u1" 0) ([])) (Atom
    "eq_sigT_rect.u1" 0)) ((:) (Clause ((:) (Atom "projT2_eq.u1" 0) ([]))
    (Atom "eq_sigT_rect.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT.u1" 0) ([]))
    (Atom "eq_sigT_rect.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT_rec.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_sigT_rec.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u0" 0)
    ([])) (Atom "eq_sigT_rec.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT_rec.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_sigT_rec.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u1" 0)
    ([])) (Atom "eq_sigT_rec.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT_ind.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_sigT_ind.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rec.u0" 0)
    ([])) (Atom "eq_sigT_ind.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT_ind.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_sigT_ind.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rec.u1" 0)
    ([])) (Atom "eq_sigT_ind.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rect.u2" 0) ([])) (Atom "eq_sigT_rect_existT_l.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_rect_existT_l.u1" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "eq_sigT_rect_existT_l.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT_rect_existT_l.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_existT_l.u0" 0) ([])) (Atom
    "eq_sigT_rect_existT_l.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u0"
    0) ([])) (Atom "eq_sigT_rect_existT_l.u1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "eq_sigT_rect_existT_l.u2" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT_rect_existT_l.u2" 0))
    ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "eq_sigT_rect_existT_l.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_rect_existT_l.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_existT_l.u1" 0) ([])) (Atom
    "eq_sigT_rect_existT_l.u2" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u1"
    0) ([])) (Atom "eq_sigT_rect_existT_l.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rect.u2" 0) ([])) (Atom "eq_sigT_rect_existT_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_rect_existT_r.u1" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "eq_sigT_rect_existT_r.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT_rect_existT_r.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_existT_r.u0" 0) ([])) (Atom
    "eq_sigT_rect_existT_r.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u0"
    0) ([])) (Atom "eq_sigT_rect_existT_r.u1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "eq_sigT_rect_existT_r.u2" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT_rect_existT_r.u2" 0))
    ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "eq_sigT_rect_existT_r.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_rect_existT_r.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_existT_r.u1" 0) ([])) (Atom
    "eq_sigT_rect_existT_r.u2" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u1"
    0) ([])) (Atom "eq_sigT_rect_existT_r.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rect.u2" 0) ([])) (Atom "eq_sigT_rect_existT.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_rect_existT.u1" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "eq_sigT_rect_existT.u1"
    0)) ((:) (Clause ((:) (Atom "eq_existT_curried.u0" 0) ([])) (Atom
    "eq_sigT_rect_existT.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u0" 0)
    ([])) (Atom "eq_sigT_rect_existT.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "eq_sigT_rect_existT.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT_rect_existT.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_sigT_rect_existT.u2" 0))
    ((:) (Clause ((:) (Atom "eq_existT_curried.u1" 0) ([])) (Atom
    "eq_sigT_rect_existT.u2" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u1" 0)
    ([])) (Atom "eq_sigT_rect_existT.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "eq_sigT_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "eq_sigT_rect_uncurried.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "eq_sigT_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT.u0" 0)
    ([])) (Atom "eq_sigT_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rect.u0" 0) ([])) (Atom "eq_sigT_rect_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_rect_uncurried.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0)
    ([])) (Atom "eq_sigT_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_rect_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT.u1" 0) ([])) (Atom
    "eq_sigT_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT_rect.u1"
    0) ([])) (Atom "eq_sigT_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rect.u2" 0) ([])) (Atom "eq_sigT_rect_uncurried.u2" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_rec_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "eq_sigT_rec_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rect_uncurried.u0" 0) ([])) (Atom "eq_sigT_rec_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_rec_uncurried.u1"
    0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "eq_sigT_rec_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rect_uncurried.u1" 0) ([])) (Atom "eq_sigT_rec_uncurried.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_ind_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "eq_sigT_ind_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rec_uncurried.u0" 0) ([])) (Atom "eq_sigT_ind_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_ind_uncurried.u1"
    0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "eq_sigT_ind_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT_rec_uncurried.u1" 0) ([])) (Atom "eq_sigT_ind_uncurried.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_hprop_iff.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_sigT_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_sigT_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT_hprop_iff.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT_hprop.u0" 0) ([])) (Atom
    "eq_sigT_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT_hprop_iff.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "eq_sigT_hprop_iff.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1"
    0) ([])) (Atom "eq_sigT_hprop_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_hprop_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT_hprop.u1" 0) ([])) (Atom
    "eq_sigT_hprop_iff.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT_nondep.u0" 0)) ((:) (Clause ((:) (Atom "rew_const.u0" 0) ([]))
    (Atom "eq_sigT_nondep.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([]))
    (Atom "eq_sigT_nondep.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT_nondep.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_sigT.u0" 0) ([])) (Atom "eq_sigT_nondep.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT_nondep.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT_nondep.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_sigT_nondep.u1" 0)) ((:) (Clause ((:) (Atom "rew_const.u1" 0) ([]))
    (Atom "eq_sigT_nondep.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "eq_sigT_nondep.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT_nondep.u1" 0)) ((:) (Clause
    ((:) (Atom "eq_sigT.u1" 0) ([])) (Atom "eq_sigT_nondep.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_sigT.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_sigT.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "rew_sigT.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT.u0" 0) ([])) (Atom "rew_sigT.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "rew_sigT.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "proj1_sig_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "proj1_sig_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "proj1_sig_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "proj1_sig_eq.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "proj2_sig_eq.u0" 0))
    ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "proj2_sig_eq.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "proj2_sig_eq.u0" 0)) ((:) (Clause ((:) (Atom "proj1_sig_eq.u0" 0) ([]))
    (Atom "proj2_sig_eq.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_exist_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0)
    ([])) (Atom "eq_exist_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "eq_sig_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0"
    0) ([])) (Atom "eq_sig_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_exist_uncurried.u0" 0) ([])) (Atom
    "eq_sig_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_exist_curried.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "eq_exist_curried.u0" 0)) ((:) (Clause ((:) (Atom "eq_sig_uncurried.u0"
    0) ([])) (Atom "eq_exist_curried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "eq_sig.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "eq_sig.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0)
    ([])) (Atom "eq_sig.u0" 0)) ((:) (Clause ((:) (Atom "eq_sig_uncurried.u0"
    0) ([])) (Atom "eq_sig.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_exist_l.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "eq_exist_l.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([]))
    (Atom "eq_exist_l.u0" 0)) ((:) (Clause ((:) (Atom "eq_sig.u0" 0) ([]))
    (Atom "eq_exist_l.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_exist_r.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "eq_exist_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([]))
    (Atom "eq_exist_r.u0" 0)) ((:) (Clause ((:) (Atom "eq_sig.u0" 0) ([]))
    (Atom "eq_exist_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sig_rect.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "eq_sig_rect.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0)
    ([])) (Atom "eq_sig_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "proj1_sig_eq.u0" 0) ([])) (Atom "eq_sig_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "proj2_sig_eq.u0" 0) ([])) (Atom "eq_sig_rect.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_sig.u0" 0) ([])) (Atom "eq_sig_rect.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig_rec.u0" 0)) ((:) (Clause ((:)
    (Atom "sig.u0" 0) ([])) (Atom "eq_sig_rec.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig_rect.u0" 0) ([])) (Atom "eq_sig_rec.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_sig_ind.u0" 0)) ((:) (Clause ((:) (Atom
    "sig.u0" 0) ([])) (Atom "eq_sig_ind.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig_rec.u0" 0) ([])) (Atom "eq_sig_ind.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_sig_rect.u1" 0) ([])) (Atom "eq_sig_rect_exist_l.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig_rect_exist_l.u1" 0))
    ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "eq_sig_rect_exist_l.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "eq_sig_rect_exist_l.u1" 0)) ((:) (Clause ((:) (Atom "eq_exist_l.u0" 0)
    ([])) (Atom "eq_sig_rect_exist_l.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sig_rect.u0" 0) ([])) (Atom "eq_sig_rect_exist_l.u1" 0)) ((:) (Clause
    ((:) (Atom "eq_sig_rect.u1" 0) ([])) (Atom "eq_sig_rect_exist_r.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig_rect_exist_r.u1"
    0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "eq_sig_rect_exist_r.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16"
    0) ([])) (Atom "eq_sig_rect_exist_r.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_exist_r.u0" 0) ([])) (Atom "eq_sig_rect_exist_r.u1" 0)) ((:) (Clause
    ((:) (Atom "eq_sig_rect.u0" 0) ([])) (Atom "eq_sig_rect_exist_r.u1" 0))
    ((:) (Clause ((:) (Atom "eq_sig_rect.u1" 0) ([])) (Atom
    "eq_sig_rect_exist.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sig_rect_exist.u1" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "eq_sig_rect_exist.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_exist_curried.u0" 0) ([])) (Atom "eq_sig_rect_exist.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sig_rect.u0" 0) ([])) (Atom "eq_sig_rect_exist.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sig_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "eq_sig_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig_rect_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sig.u0" 0) ([])) (Atom "eq_sig_rect_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "eq_sig_rect.u0" 0) ([])) (Atom
    "eq_sig_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq_sig_rect.u1"
    0) ([])) (Atom "eq_sig_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "eq_sig_rec_uncurried.u0" 0)) ((:) (Clause ((:)
    (Atom "sig.u0" 0) ([])) (Atom "eq_sig_rec_uncurried.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_sig_rect_uncurried.u0" 0) ([])) (Atom
    "eq_sig_rec_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sig_ind_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0)
    ([])) (Atom "eq_sig_ind_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig_rec_uncurried.u0" 0) ([])) (Atom "eq_sig_ind_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig_hprop.u0" 0)) ((:)
    (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "eq_sig_hprop.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig_hprop.u0"
    0)) ((:) (Clause ((:) (Atom "eq_sig.u0" 0) ([])) (Atom "eq_sig_hprop.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sig_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "eq_sig_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "sig.u0" 0) ([])) (Atom "eq_sig_uncurried_iff.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig_uncurried_iff.u0" 0))
    ((:) (Clause ((:) (Atom "eq_sig_uncurried.u0" 0) ([])) (Atom
    "eq_sig_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sig_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_sig_hprop_iff.u0" 0)) ((:) (Clause
    ((:) (Atom "sig.u0" 0) ([])) (Atom "eq_sig_hprop_iff.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig_hprop_iff.u0" 0))
    ((:) (Clause ((:) (Atom "eq_sig_hprop.u0" 0) ([])) (Atom
    "eq_sig_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_sig.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_sig.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "rew_sig.u1" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "rew_sig.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([]))
    (Atom "rew_sig.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "sigT_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0)
    ([])) (Atom "sigT_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0"
    0) ([])) (Atom "sigT_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT2.u0" 0) ([])) (Atom "sigT_of_sigT2_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom "sigT_of_sigT2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "sigT_of_sigT2_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "sigT_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0) ([]))
    (Atom "sigT_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "sigT_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u1" 0) ([])) (Atom "sigT_of_sigT2_eq.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "sigT_of_sigT2_eq.u2" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "sigT_of_sigT2_eq.u2" 0))
    ((:) (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "sigT_of_sigT2_eq.u2"
    0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom
    "sigT_of_sigT2_eq.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "projT1_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([]))
    (Atom "projT1_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "projT1_of_sigT2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "projT1_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom "projT1_eq.u0" 0)
    ([])) (Atom "projT1_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2_eq.u0" 0) ([])) (Atom "projT1_of_sigT2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT1_of_sigT2_eq.u1" 0))
    ((:) (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "projT1_of_sigT2_eq.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom
    "projT1_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0)
    ([])) (Atom "projT1_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "projT1_eq.u1" 0) ([])) (Atom "projT1_of_sigT2_eq.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT_of_sigT2_eq.u1" 0) ([])) (Atom "projT1_of_sigT2_eq.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "projT1_of_sigT2_eq.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0) ([]))
    (Atom "projT1_of_sigT2_eq.u2" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u2" 0) ([])) (Atom "projT1_of_sigT2_eq.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2_eq.u2" 0) ([])) (Atom
    "projT1_of_sigT2_eq.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "projT2_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0)
    ([])) (Atom "projT2_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "projT2_of_sigT2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "projT2_of_sigT2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "projT1_of_sigT2_eq.u0" 0) ([])) (Atom "projT2_of_sigT2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT2_of_sigT2_eq.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "projT2_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0) ([]))
    (Atom "projT2_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "projT2_of_sigT2_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom
    "projT2_of_sigT2_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "projT1_of_sigT2_eq.u1" 0) ([])) (Atom "projT2_of_sigT2_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT2_of_sigT2_eq.u2" 0))
    ((:) (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "projT2_of_sigT2_eq.u2"
    0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom
    "projT2_of_sigT2_eq.u2" 0)) ((:) (Clause ((:) (Atom
    "projT1_of_sigT2_eq.u2" 0) ([])) (Atom "projT2_of_sigT2_eq.u2" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT3_eq.u0" 0)) ((:) (Clause
    ((:) (Atom "sigT2.u0" 0) ([])) (Atom "projT3_eq.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "projT3_eq.u0" 0)) ((:) (Clause
    ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom "projT3_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.29" 0) ([])) (Atom "projT3_eq.u0" 0))
    ((:) (Clause ((:) (Atom "projT1_of_sigT2_eq.u0" 0) ([])) (Atom
    "projT3_eq.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "projT3_eq.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom
    "projT3_eq.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([]))
    (Atom "projT3_eq.u1" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0)
    ([])) (Atom "projT3_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "projT3_eq.u1" 0)) ((:) (Clause ((:)
    (Atom "projT1_of_sigT2_eq.u1" 0) ([])) (Atom "projT3_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "projT3_eq.u2" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "projT3_eq.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "projT3_eq.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom "projT3_eq.u2" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "projT3_eq.u2" 0)) ((:) (Clause ((:) (Atom "projT1_of_sigT2_eq.u2" 0)
    ([])) (Atom "projT3_eq.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0)
    ([])) (Atom "eq_existT2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "eq_existT2_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT2_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_existT2_uncurried.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_existT2_uncurried.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9"
    0) ([])) (Atom "eq_existT2_uncurried.u2" 0)) ((:) (Clause ((:) (Atom
    "sigT2.u2" 0) ([])) (Atom "eq_existT2_uncurried.u2" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_uncurried.u0" 0)) ((:) (Clause
    ((:) (Atom "sigT2.u0" 0) ([])) (Atom "eq_sigT2_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "eq_sigT2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0)
    ([])) (Atom "eq_sigT2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "eq_sigT2_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_existT2_uncurried.u0" 0) ([])) (Atom
    "eq_sigT2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_sigT2_uncurried.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom
    "eq_sigT2_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_existT2_uncurried.u1" 0) ([])) (Atom
    "eq_sigT2_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_uncurried.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_uncurried.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "eq_sigT2_uncurried.u2" 0))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom
    "eq_sigT2_uncurried.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.30"
    0) ([])) (Atom "eq_sigT2_uncurried.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_existT2_uncurried.u2" 0) ([])) (Atom "eq_sigT2_uncurried.u2" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT2_curried.u0" 0))
    ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom "eq_existT2_curried.u0"
    0)) ((:) (Clause ((:) (Atom "eq_sigT2_uncurried.u0" 0) ([])) (Atom
    "eq_existT2_curried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT2_curried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT2_curried.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_existT2_curried.u1" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2_uncurried.u1" 0) ([])) (Atom
    "eq_existT2_curried.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT2_curried.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT2_curried.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "eq_existT2_curried.u2" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2_uncurried.u2" 0) ([])) (Atom
    "eq_existT2_curried.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom
    "eq_sigT2.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([]))
    (Atom "eq_sigT2.u0" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0)
    ([])) (Atom "eq_sigT2.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "eq_sigT2.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_sigT2_uncurried.u0" 0) ([])) (Atom "eq_sigT2.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_sigT2.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT2.u1" 0))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom "eq_sigT2.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_sigT2.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT2_uncurried.u1" 0)
    ([])) (Atom "eq_sigT2.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0)
    ([])) (Atom "eq_sigT2.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0) ([]))
    (Atom "eq_sigT2.u2" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0)
    ([])) (Atom "eq_sigT2.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2.u2" 0)) ((:) (Clause ((:)
    (Atom "eq_sigT2_uncurried.u2" 0) ([])) (Atom "eq_sigT2.u2" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT2_l.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom "eq_existT2_l.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "eq_existT2_l.u0"
    0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "eq_existT2_l.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.29" 0)
    ([])) (Atom "eq_existT2_l.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u0"
    0) ([])) (Atom "eq_existT2_l.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "eq_existT2_l.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT2_l.u1" 0)) ((:) (Clause ((:)
    (Atom "sigT2.u1" 0) ([])) (Atom "eq_existT2_l.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "eq_existT2_l.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom "eq_existT2_l.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_existT2_l.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u1" 0) ([]))
    (Atom "eq_existT2_l.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT2_l.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0)
    ([])) (Atom "eq_existT2_l.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_existT2_l.u2" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u2" 0) ([])) (Atom "eq_existT2_l.u2" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.30" 0) ([])) (Atom "eq_existT2_l.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2.u2" 0) ([])) (Atom "eq_existT2_l.u2" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_existT2_r.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom "eq_existT2_r.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "eq_existT2_r.u0"
    0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "eq_existT2_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.29" 0)
    ([])) (Atom "eq_existT2_r.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u0"
    0) ([])) (Atom "eq_existT2_r.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "eq_existT2_r.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_existT2_r.u1" 0)) ((:) (Clause ((:)
    (Atom "sigT2.u1" 0) ([])) (Atom "eq_existT2_r.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "eq_existT2_r.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom "eq_existT2_r.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_existT2_r.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u1" 0) ([]))
    (Atom "eq_existT2_r.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_existT2_r.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0)
    ([])) (Atom "eq_existT2_r.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_existT2_r.u2" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u2" 0) ([])) (Atom "eq_existT2_r.u2" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.30" 0) ([])) (Atom "eq_existT2_r.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2.u2" 0) ([])) (Atom "eq_existT2_r.u2" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_hprop.u0" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom "eq_sigT2_hprop.u0" 0))
    ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom "eq_sigT2_hprop.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "eq_sigT2_hprop.u0" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0)
    ([])) (Atom "eq_sigT2_hprop.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "eq_sigT2_hprop.u0" 0)) ((:) (Clause
    ((:) (Atom "projT1_eq.u0" 0) ([])) (Atom "eq_sigT2_hprop.u0" 0)) ((:)
    (Clause ((:) (Atom "projT2_eq.u0" 0) ([])) (Atom "eq_sigT2_hprop.u0" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2.u0" 0) ([])) (Atom "eq_sigT2_hprop.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_hprop.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT2_hprop.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom
    "eq_sigT2_hprop.u1" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_hprop.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_hprop.u1" 0)) ((:) (Clause
    ((:) (Atom "eq_sigT2.u2" 0) ([])) (Atom "eq_sigT2_hprop.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_hprop.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_sigT2_hprop.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_sigT2_hprop.u2" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom
    "eq_sigT2_hprop.u2" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_hprop.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_hprop.u2" 0)) ((:) (Clause
    ((:) (Atom "projT1_eq.u1" 0) ([])) (Atom "eq_sigT2_hprop.u2" 0)) ((:)
    (Clause ((:) (Atom "projT2_eq.u1" 0) ([])) (Atom "eq_sigT2_hprop.u2" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2.u1" 0) ([])) (Atom "eq_sigT2_hprop.u2"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "eq_sigT2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT2.u0" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u0" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.29" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_uncurried.u0" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2_uncurried.u1" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_uncurried_iff.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_uncurried_iff.u2" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u2" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u2" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_sigT2_uncurried_iff.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_uncurried.u2" 0) ([])) (Atom "eq_sigT2_uncurried_iff.u2" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect.u0" 0))
    ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom "eq_sigT2_rect.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "eq_sigT2_rect.u0" 0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0)
    ([])) (Atom "eq_sigT2_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "eq_sigT2_rect.u0" 0)) ((:) (Clause
    ((:) (Atom "projT1_of_sigT2_eq.u0" 0) ([])) (Atom "eq_sigT2_rect.u0" 0))
    ((:) (Clause ((:) (Atom "projT2_of_sigT2_eq.u0" 0) ([])) (Atom
    "eq_sigT2_rect.u0" 0)) ((:) (Clause ((:) (Atom "projT3_eq.u0" 0) ([]))
    (Atom "eq_sigT2_rect.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u0" 0)
    ([])) (Atom "eq_sigT2_rect.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "eq_sigT2_rect.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_rect.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_sigT2_rect.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT2_rect.u1" 0))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom
    "eq_sigT2_rect.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0)
    ([])) (Atom "eq_sigT2_rect.u1" 0)) ((:) (Clause ((:) (Atom
    "projT1_of_sigT2_eq.u1" 0) ([])) (Atom "eq_sigT2_rect.u1" 0)) ((:)
    (Clause ((:) (Atom "projT2_of_sigT2_eq.u1" 0) ([])) (Atom
    "eq_sigT2_rect.u1" 0)) ((:) (Clause ((:) (Atom "projT3_eq.u1" 0) ([]))
    (Atom "eq_sigT2_rect.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_rect.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "eq_sigT2_rect.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_rect.u2" 0)) ((:) (Clause
    ((:) (Atom "sigT2.u2" 0) ([])) (Atom "eq_sigT2_rect.u2" 0)) ((:) (Clause
    ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom "eq_sigT2_rect.u2" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_rect.u2"
    0)) ((:) (Clause ((:) (Atom "projT1_of_sigT2_eq.u2" 0) ([])) (Atom
    "eq_sigT2_rect.u2" 0)) ((:) (Clause ((:) (Atom "projT2_of_sigT2_eq.u2" 0)
    ([])) (Atom "eq_sigT2_rect.u2" 0)) ((:) (Clause ((:) (Atom "projT3_eq.u2"
    0) ([])) (Atom "eq_sigT2_rect.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2.u2" 0) ([])) (Atom "eq_sigT2_rect.u2" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rec.u0" 0)) ((:) (Clause ((:)
    (Atom "sigT2.u0" 0) ([])) (Atom "eq_sigT2_rec.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_sigT2_rect.u0" 0) ([])) (Atom "eq_sigT2_rec.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rec.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_sigT2_rec.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect.u1" 0) ([])) (Atom "eq_sigT2_rec.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rec.u2" 0))
    ((:) (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "eq_sigT2_rec.u2" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2_rect.u2" 0) ([])) (Atom
    "eq_sigT2_rec.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_ind.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_ind.u0" 0)) ((:) (Clause ((:) (Atom "eq_sigT2_rec.u0" 0) ([]))
    (Atom "eq_sigT2_ind.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_ind.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0) ([]))
    (Atom "eq_sigT2_ind.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT2_rec.u1" 0)
    ([])) (Atom "eq_sigT2_ind.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "eq_sigT2_ind.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_ind.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rec.u2" 0) ([])) (Atom "eq_sigT2_ind.u2" 0)) ((:) (Clause ((:)
    (Atom "eq_sigT2_rect.u3" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0)
    ([])) (Atom "eq_sigT2_rect_existT2_l.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_existT2_l.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u2"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_rect_existT2_l.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_existT2_l.u1" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u1" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u2" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u3"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u3" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_rect_existT2_l.u3" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u2" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u3" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u3" 0)) ((:) (Clause ((:) (Atom
    "eq_existT2_l.u2" 0) ([])) (Atom "eq_sigT2_rect_existT2_l.u3" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect.u2" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_l.u3" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u3" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u1"
    0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_existT2_r.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u2"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_rect_existT2_r.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_existT2_r.u1" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u1" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u2" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u3"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u3" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_rect_existT2_r.u3" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u2" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u3" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u3" 0)) ((:) (Clause ((:) (Atom
    "eq_existT2_r.u2" 0) ([])) (Atom "eq_sigT2_rect_existT2_r.u3" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect.u2" 0) ([])) (Atom
    "eq_sigT2_rect_existT2_r.u3" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u3" 0) ([])) (Atom "eq_sigT2_rect_existT2.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2.u1" 0))
    ((:) (Clause ((:) (Atom "sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_existT2_curried.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2.u1" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2_rect.u0" 0) ([])) (Atom
    "eq_sigT2_rect_existT2.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_rect_existT2.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_rect_existT2.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_sigT2_rect_existT2.u2"
    0)) ((:) (Clause ((:) (Atom "eq_existT2_curried.u1" 0) ([])) (Atom
    "eq_sigT2_rect_existT2.u2" 0)) ((:) (Clause ((:) (Atom "eq_sigT2_rect.u1"
    0) ([])) (Atom "eq_sigT2_rect_existT2.u2" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_existT2.u3" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_rect_existT2.u3" 0))
    ((:) (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom
    "eq_sigT2_rect_existT2.u3" 0)) ((:) (Clause ((:) (Atom
    "eq_existT2_curried.u2" 0) ([])) (Atom "eq_sigT2_rect_existT2.u3" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2_rect.u2" 0) ([])) (Atom
    "eq_sigT2_rect_existT2.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0"
    0) ([])) (Atom "eq_sigT2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.29" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u0" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.30" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2.u1" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u1" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u2"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_rect_uncurried.u2" 0)) ((:) (Clause ((:) (Atom
    "sigT_of_sigT2.u2" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u2" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u2" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_rect_uncurried.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect.u2" 0) ([])) (Atom "eq_sigT2_rect_uncurried.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_sigT2_rect.u3" 0) ([])) (Atom
    "eq_sigT2_rect_uncurried.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_rec_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0"
    0) ([])) (Atom "eq_sigT2_rec_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_uncurried.u0" 0) ([])) (Atom "eq_sigT2_rec_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_rec_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_rec_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_uncurried.u1" 0) ([])) (Atom "eq_sigT2_rec_uncurried.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_rec_uncurried.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_rec_uncurried.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rect_uncurried.u2" 0) ([])) (Atom "eq_sigT2_rec_uncurried.u2"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_ind_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sigT2.u0" 0)
    ([])) (Atom "eq_sigT2_ind_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rec_uncurried.u0" 0) ([])) (Atom "eq_sigT2_ind_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_ind_uncurried.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_ind_uncurried.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rec_uncurried.u1" 0) ([])) (Atom "eq_sigT2_ind_uncurried.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_ind_uncurried.u2" 0)) ((:) (Clause ((:) (Atom "sigT2.u2" 0)
    ([])) (Atom "eq_sigT2_ind_uncurried.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2_rec_uncurried.u2" 0) ([])) (Atom "eq_sigT2_ind_uncurried.u2"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_sigT2_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10"
    0) ([])) (Atom "eq_sigT2_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "eq_sigT2_hprop_iff.u0" 0)) ((:) (Clause ((:)
    (Atom "sigT2.u0" 0) ([])) (Atom "eq_sigT2_hprop_iff.u0" 0)) ((:) (Clause
    ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom "eq_sigT2_hprop_iff.u0" 0))
    ((:) (Clause ((:) (Atom "eq_sigT2_hprop.u0" 0) ([])) (Atom
    "eq_sigT2_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_hprop_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_sigT2_hprop_iff.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "eq_sigT2_hprop_iff.u1" 0))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom
    "eq_sigT2_hprop_iff.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT2_hprop.u1"
    0) ([])) (Atom "eq_sigT2_hprop_iff.u1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "eq_sigT2_hprop_iff.u2" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "eq_sigT2_hprop_iff.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "eq_sigT2_hprop_iff.u2" 0))
    ((:) (Clause ((:) (Atom "sigT2.u1" 0) ([])) (Atom "eq_sigT2_hprop_iff.u2"
    0)) ((:) (Clause ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom
    "eq_sigT2_hprop_iff.u2" 0)) ((:) (Clause ((:) (Atom "eq_sigT2_hprop.u2"
    0) ([])) (Atom "eq_sigT2_hprop_iff.u2" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "eq_sigT2_nondep.u0" 0)) ((:) (Clause ((:) (Atom
    "rew_const.u0" 0) ([])) (Atom "eq_sigT2_nondep.u0" 0)) ((:) (Clause ((:)
    (Atom "sigT2.u0" 0) ([])) (Atom "eq_sigT2_nondep.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "eq_sigT2_nondep.u0" 0))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom
    "eq_sigT2_nondep.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.29" 0)
    ([])) (Atom "eq_sigT2_nondep.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2.u0" 0) ([])) (Atom "eq_sigT2_nondep.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_sigT2_nondep.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "eq_sigT2_nondep.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_sigT2_nondep.u1" 0)) ((:) (Clause ((:) (Atom "rew_const.u1" 0) ([]))
    (Atom "eq_sigT2_nondep.u1" 0)) ((:) (Clause ((:) (Atom "sigT2.u1" 0)
    ([])) (Atom "eq_sigT2_nondep.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "eq_sigT2_nondep.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT_of_sigT2.u1" 0) ([])) (Atom "eq_sigT2_nondep.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0) ([])) (Atom
    "eq_sigT2_nondep.u1" 0)) ((:) (Clause ((:) (Atom "eq_sigT2.u1" 0) ([]))
    (Atom "eq_sigT2_nondep.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sigT2_nondep.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9"
    0) ([])) (Atom "eq_sigT2_nondep.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "eq_sigT2_nondep.u2" 0)) ((:) (Clause
    ((:) (Atom "rew_const.u1" 0) ([])) (Atom "eq_sigT2_nondep.u2" 0)) ((:)
    (Clause ((:) (Atom "sigT2.u2" 0) ([])) (Atom "eq_sigT2_nondep.u2" 0))
    ((:) (Clause ((:) (Atom "sigT_of_sigT2.u2" 0) ([])) (Atom
    "eq_sigT2_nondep.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.30" 0)
    ([])) (Atom "eq_sigT2_nondep.u2" 0)) ((:) (Clause ((:) (Atom
    "eq_sigT2.u2" 0) ([])) (Atom "eq_sigT2_nondep.u2" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "rew_sigT2.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "rew_sigT2.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "rew_sigT2.u1" 0)) ((:) (Clause ((:)
    (Atom "sigT2.u0" 0) ([])) (Atom "rew_sigT2.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.22" 0) ([])) (Atom "rew_sigT2.u1" 0)) ((:) (Clause
    ((:) (Atom "sigT_of_sigT2.u0" 0) ([])) (Atom "rew_sigT2.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.29" 0) ([])) (Atom "rew_sigT2.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "sig_of_sig2_eq.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([]))
    (Atom "sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "proj1_sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0)
    ([])) (Atom "proj1_sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "proj1_sig_of_sig2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "proj1_sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom "proj1_sig_eq.u0"
    0) ([])) (Atom "proj1_sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "sig_of_sig2_eq.u0" 0) ([])) (Atom "proj1_sig_of_sig2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "proj2_sig_of_sig2_eq.u0" 0))
    ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "proj2_sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "proj2_sig_of_sig2_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "proj2_sig_of_sig2_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "proj1_sig_of_sig2_eq.u0" 0) ([])) (Atom "proj2_sig_of_sig2_eq.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "proj3_sig_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom "proj3_sig_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "proj3_sig_eq.u0"
    0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "proj3_sig_eq.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.21" 0)
    ([])) (Atom "proj3_sig_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "proj1_sig_of_sig2_eq.u0" 0) ([])) (Atom "proj3_sig_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_exist2_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom "eq_exist2_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "eq_sig2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16"
    0) ([])) (Atom "eq_sig2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "sig_of_sig2.u0" 0) ([])) (Atom "eq_sig2_uncurried.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "eq_exist2_uncurried.u0" 0) ([])) (Atom
    "eq_sig2_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "eq_exist2_curried.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([]))
    (Atom "eq_exist2_curried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_uncurried.u0" 0) ([])) (Atom "eq_exist2_curried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2.u0" 0)) ((:) (Clause
    ((:) (Atom "sig2.u0" 0) ([])) (Atom "eq_sig2.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig2.u0" 0)) ((:) (Clause
    ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom "eq_sig2.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sig2_uncurried.u0" 0) ([])) (Atom "eq_sig2.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_exist2_l.u0" 0)) ((:)
    (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom "eq_exist2_l.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "eq_exist2_l.u0"
    0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "eq_exist2_l.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.21" 0)
    ([])) (Atom "eq_exist2_l.u0" 0)) ((:) (Clause ((:) (Atom "eq_sig2.u0" 0)
    ([])) (Atom "eq_exist2_l.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_exist2_r.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([]))
    (Atom "eq_exist2_r.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16"
    0) ([])) (Atom "eq_exist2_r.u0" 0)) ((:) (Clause ((:) (Atom
    "sig_of_sig2.u0" 0) ([])) (Atom "eq_exist2_r.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.21" 0) ([])) (Atom "eq_exist2_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sig2.u0" 0) ([])) (Atom "eq_exist2_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_hprop.u0" 0)) ((:)
    (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "eq_sig2_hprop.u0" 0)) ((:)
    (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom "eq_sig2_hprop.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig2_hprop.u0"
    0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "eq_sig2_hprop.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.21" 0)
    ([])) (Atom "eq_sig2_hprop.u0" 0)) ((:) (Clause ((:) (Atom
    "proj1_sig_eq.u0" 0) ([])) (Atom "eq_sig2_hprop.u0" 0)) ((:) (Clause ((:)
    (Atom "proj2_sig_eq.u0" 0) ([])) (Atom "eq_sig2_hprop.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sig2.u0" 0) ([])) (Atom "eq_sig2_hprop.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_uncurried_iff.u0"
    0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "eq_sig2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([]))
    (Atom "eq_sig2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig2_uncurried_iff.u0" 0)) ((:)
    (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "eq_sig2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2_uncurried_iff.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sig2_uncurried.u0" 0) ([])) (Atom
    "eq_sig2_uncurried_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "eq_sig2_rect.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([]))
    (Atom "eq_sig2_rect.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16"
    0) ([])) (Atom "eq_sig2_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "sig_of_sig2.u0" 0) ([])) (Atom "eq_sig2_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2_rect.u0" 0)) ((:)
    (Clause ((:) (Atom "proj1_sig_of_sig2_eq.u0" 0) ([])) (Atom
    "eq_sig2_rect.u0" 0)) ((:) (Clause ((:) (Atom "proj2_sig_of_sig2_eq.u0"
    0) ([])) (Atom "eq_sig2_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "proj3_sig_eq.u0" 0) ([])) (Atom "eq_sig2_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_sig2.u0" 0) ([])) (Atom "eq_sig2_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_rec.u0" 0)) ((:) (Clause ((:) (Atom
    "sig2.u0" 0) ([])) (Atom "eq_sig2_rec.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_rect.u0" 0) ([])) (Atom "eq_sig2_rec.u0" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_ind.u0" 0)) ((:) (Clause ((:) (Atom
    "sig2.u0" 0) ([])) (Atom "eq_sig2_ind.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_rec.u0" 0) ([])) (Atom "eq_sig2_ind.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_sig2_rect.u1" 0) ([])) (Atom "eq_sig2_rect_exist2_l.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_rect_exist2_l.u1"
    0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "eq_sig2_rect_exist2_l.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig2_rect_exist2_l.u1" 0)) ((:)
    (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "eq_sig2_rect_exist2_l.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2_rect_exist2_l.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_exist2_l.u0" 0) ([])) (Atom
    "eq_sig2_rect_exist2_l.u1" 0)) ((:) (Clause ((:) (Atom "eq_sig2_rect.u0"
    0) ([])) (Atom "eq_sig2_rect_exist2_l.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_rect.u1" 0) ([])) (Atom "eq_sig2_rect_exist2_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_rect_exist2_r.u1" 0))
    ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "eq_sig2_rect_exist2_r.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "eq_sig2_rect_exist2_r.u1" 0)) ((:)
    (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom
    "eq_sig2_rect_exist2_r.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2_rect_exist2_r.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_exist2_r.u0" 0) ([])) (Atom
    "eq_sig2_rect_exist2_r.u1" 0)) ((:) (Clause ((:) (Atom "eq_sig2_rect.u0"
    0) ([])) (Atom "eq_sig2_rect_exist2_r.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_rect.u1" 0) ([])) (Atom "eq_sig2_rect_exist2.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_rect_exist2.u1" 0))
    ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom "eq_sig2_rect_exist2.u1"
    0)) ((:) (Clause ((:) (Atom "eq_exist2_curried.u0" 0) ([])) (Atom
    "eq_sig2_rect_exist2.u1" 0)) ((:) (Clause ((:) (Atom "eq_sig2_rect.u0" 0)
    ([])) (Atom "eq_sig2_rect_exist2.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "eq_sig2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "sig2.u0" 0) ([])) (Atom "eq_sig2_rect_uncurried.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "eq_sig2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0"
    0) ([])) (Atom "eq_sig2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2_rect_uncurried.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_sig2.u0" 0) ([])) (Atom
    "eq_sig2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom "eq_sig2_rect.u0"
    0) ([])) (Atom "eq_sig2_rect_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_rect.u1" 0) ([])) (Atom "eq_sig2_rect_uncurried.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_rec_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "eq_sig2_rec_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_rect_uncurried.u0" 0) ([])) (Atom "eq_sig2_rec_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_ind_uncurried.u0"
    0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom
    "eq_sig2_ind_uncurried.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_sig2_rec_uncurried.u0" 0) ([])) (Atom "eq_sig2_ind_uncurried.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_hprop_iff.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "eq_sig2_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "eq_sig2_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom "sig2.u0" 0)
    ([])) (Atom "eq_sig2_hprop_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "sig_of_sig2.u0" 0) ([])) (Atom "eq_sig2_hprop_iff.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_sig2_hprop.u0" 0) ([])) (Atom "eq_sig2_hprop_iff.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "eq_sig2_nondep.u0" 0))
    ((:) (Clause ((:) (Atom "rew_const.u0" 0) ([])) (Atom "eq_sig2_nondep.u0"
    0)) ((:) (Clause ((:) (Atom "sig2.u0" 0) ([])) (Atom "eq_sig2_nondep.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "eq_sig2_nondep.u0" 0)) ((:) (Clause ((:) (Atom "sig_of_sig2.u0" 0) ([]))
    (Atom "eq_sig2_nondep.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.21" 0) ([])) (Atom "eq_sig2_nondep.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_sig2.u0" 0) ([])) (Atom "eq_sig2_nondep.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_sig2.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "rew_sig2.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "rew_sig2.u1" 0)) ((:) (Clause
    ((:) (Atom "sig2.u0" 0) ([])) (Atom "rew_sig2.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.16" 0) ([])) (Atom "rew_sig2.u1" 0)) ((:) (Clause
    ((:) (Atom "sig_of_sig2.u0" 0) ([])) (Atom "rew_sig2.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.21" 0) ([])) (Atom "rew_sig2.u1" 0)) ((:)
    (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "Coq.Init.Specif.771" 0))
    ((:) (Clause ((:) (Atom "well_founded_induction_type.u0" 0) ([])) (Atom
    "Wf_Z.natlike_rec2.u0" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0)
    ([])) (Atom "Wf_Z.natlike_rec2.u0" 0)) ((:) (Clause ((:) (Atom
    "well_founded_induction_type.u0" 0) ([])) (Atom "Wf_Z.natlike_rec3.u0"
    0)) ((:) (Clause ((:) (Atom "well_founded_induction_type.u0" 0) ([]))
    (Atom "Wf_Z.Zlt_0_rec.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.2"
    0) ([])) (Atom "Wf_Z.Zlt_0_rec.u0" 0)) ((:) (Clause ((:) (Atom
    "Wf_Z.Zlt_0_rec.u0" 0) ([])) (Atom "Wf_Z.Z_lt_rec.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "Wf_Z.Zlt_lower_bound_rec.u0" 0)) ((:) (Clause ((:) (Atom
    "Wf_Z.Zlt_0_rec.u0" 0) ([])) (Atom "Wf_Z.Zlt_lower_bound_rec.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Wf.1" 0) ([])) (Atom "Coq.Arith.Wf_nat.1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.11" 0) ([])) (Atom
    "Coq.Arith.Wf_nat.1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.2" 0)
    ([])) (Atom "induction_ltof1.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.11" 0) ([])) (Atom "induction_ltof1.u0" 0)) ((:)
    (Clause ((:) (Atom "induction_ltof1.u0" 0) ([])) (Atom "lt_wf_rect1.u0"
    0)) ((:) (Clause ((:) (Atom "well_founded_induction_type.u0" 0) ([]))
    (Atom "lt_wf_rect.u0" 0)) ((:) (Clause ((:) (Atom "lt_wf_rect.u0" 0)
    ([])) (Atom "lt_wf_double_rect.u0" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0)
    ([])) (Atom "has_unique_least_element.u0" 0)) ((:) (Clause ((:) (Atom
    "unique.u0" 0) ([])) (Atom "has_unique_least_element.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Zmisc.iter_nat_of_Z.u0" 0)) ((:)
    (Clause ((:) (Atom "Pnat.Pos2Nat.inj_iter.u0" 0) ([])) (Atom
    "Zmisc.iter_nat_of_Z.u0" 0)) ((:) (Clause ((:) (Atom "BinInt.Z.iter.u0"
    0) ([])) (Atom "Zmisc.iter_nat_of_Z.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.11" 0) ([])) (Atom "Zmisc.iter_nat_of_Z.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Numbers.BinNums.1" 0) ([])) (Atom
    "BinNat.N.binary_rect.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.peano_rect.u0" 0) ([])) (Atom "BinNat.N.peano_rect.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "BinNat.N.peano_rect_base.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.peano_rect.u0" 0) ([])) (Atom "BinNat.N.peano_rect_base.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "BinNat.N.peano_rect_succ.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "BinNat.N.peano_rect_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.peano_rect.u0" 0) ([])) (Atom "BinNat.N.peano_rect_succ.u0" 0))
    ((:) (Clause ((:) (Atom "BinPos.Pos.peano_rect.u0" 0) ([])) (Atom
    "BinNat.N.peano_rect_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.peano_rect_succ.u0" 0) ([])) (Atom
    "BinNat.N.peano_rect_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.peano_rect.u0" 0) ([])) (Atom "BinNat.N.recursion.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "BinNat.N.recursion_wd.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.peano_rect.u0" 0) ([])) (Atom "BinNat.N.recursion_wd.u0" 0))
    ((:) (Clause ((:) (Atom "BinNat.N.peano_rect_succ.u0" 0) ([])) (Atom
    "BinNat.N.recursion_wd.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.recursion.u0" 0) ([])) (Atom "BinNat.N.recursion_wd.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "BinNat.N.recursion_0.u0"
    0)) ((:) (Clause ((:) (Atom "BinNat.N.recursion.u0" 0) ([])) (Atom
    "BinNat.N.recursion_0.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "BinNat.N.recursion_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.peano_rect.u0" 0) ([])) (Atom "BinNat.N.recursion_succ.u0" 0))
    ((:) (Clause ((:) (Atom "BinNat.N.peano_rect_succ.u0" 0) ([])) (Atom
    "BinNat.N.recursion_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.recursion.u0" 0) ([])) (Atom "BinNat.N.recursion_succ.u0" 0))
    ((:) (Clause ((:) (Atom "BinPos.Pos.iter_swap_gen.u0" 0) ([])) (Atom
    "BinNat.N.iter_swap_gen.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.iter.u0" 0) ([])) (Atom "BinNat.N.iter_swap_gen.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "BinNat.N.iter_swap_gen.u1" 0))
    ((:) (Clause ((:) (Atom "BinPos.Pos.iter_swap_gen.u1" 0) ([])) (Atom
    "BinNat.N.iter_swap_gen.u1" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.iter.u0" 0) ([])) (Atom "BinNat.N.iter_swap_gen.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "BinNat.N.iter_swap.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "BinNat.N.iter_swap.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "BinNat.N.iter_swap.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.iter_swap_gen.u0" 0) ([])) (Atom "BinNat.N.iter_swap.u0" 0))
    ((:) (Clause ((:) (Atom "BinNat.N.iter_swap_gen.u1" 0) ([])) (Atom
    "BinNat.N.iter_swap.u0" 0)) ((:) (Clause ((:) (Atom "BinNat.N.iter.u0" 0)
    ([])) (Atom "BinNat.N.iter_swap.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "BinNat.N.iter_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "BinNat.N.iter_succ.u0" 0)) ((:) (Clause
    ((:) (Atom "BinPos.Pos.iter_succ.u0" 0) ([])) (Atom
    "BinNat.N.iter_succ.u0" 0)) ((:) (Clause ((:) (Atom "BinNat.N.iter.u0" 0)
    ([])) (Atom "BinNat.N.iter_succ.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "BinNat.N.iter_succ_r.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.iter_swap.u0" 0) ([])) (Atom "BinNat.N.iter_succ_r.u0" 0)) ((:)
    (Clause ((:) (Atom "BinNat.N.iter_succ.u0" 0) ([])) (Atom
    "BinNat.N.iter_succ_r.u0" 0)) ((:) (Clause ((:) (Atom "BinNat.N.iter.u0"
    0) ([])) (Atom "BinNat.N.iter_succ_r.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "BinNat.N.iter_add.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "BinNat.N.iter_add.u0" 0)) ((:) (Clause ((:)
    (Atom "BinNat.N.iter_succ.u0" 0) ([])) (Atom "BinNat.N.iter_add.u0" 0))
    ((:) (Clause ((:) (Atom "BinNat.N.iter.u0" 0) ([])) (Atom
    "BinNat.N.iter_add.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.iter_succ.u0" 0) ([])) (Atom "BinNat.N.iter_ind.u0" 0)) ((:)
    (Clause ((:) (Atom "BinNat.N.iter.u0" 0) ([])) (Atom
    "BinNat.N.iter_ind.u0" 0)) ((:) (Clause ((:) (Atom "BinNat.N.iter_ind.u0"
    0) ([])) (Atom "BinNat.N.iter_invariant.u0" 0)) ((:) (Clause ((:) (Atom
    "BinNat.N.iter.u0" 0) ([])) (Atom "BinNat.N.iter_invariant.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "BinPos.Pos.peano_rect_succ.u0"
    0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "BinPos.Pos.peano_rect_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.peano_rect.u0" 0) ([])) (Atom "BinPos.Pos.peano_rect_succ.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "BinPos.Pos.peano_rect_base.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.peano_rect.u0" 0) ([])) (Atom "BinPos.Pos.peano_rect_base.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "BinPos.Pos.peano_equiv.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "BinPos.Pos.peano_equiv.u0" 0)) ((:)
    (Clause ((:) (Atom "BinPos.Pos.peano_rect.u0" 0) ([])) (Atom
    "BinPos.Pos.peano_equiv.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.peano_rect_succ.u0" 0) ([])) (Atom
    "BinPos.Pos.peano_equiv.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.PeanoView_iter.u0" 0) ([])) (Atom "BinPos.Pos.peano_equiv.u0"
    0)) ((:) (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_swap_gen.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "BinPos.Pos.iter_swap_gen.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "BinPos.Pos.iter_swap_gen.u1" 0)) ((:)
    (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_swap_gen.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "BinPos.Pos.iter_swap.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "BinPos.Pos.iter_swap.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "BinPos.Pos.iter_swap.u0"
    0)) ((:) (Clause ((:) (Atom "BinPos.Pos.iter_swap_gen.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_swap.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_swap_gen.u1" 0) ([])) (Atom "BinPos.Pos.iter_swap.u0"
    0)) ((:) (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_swap.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "BinPos.Pos.iter_succ.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "BinPos.Pos.iter_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_swap.u0" 0) ([])) (Atom "BinPos.Pos.iter_succ.u0" 0))
    ((:) (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_succ.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "BinPos.Pos.iter_succ_r.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_swap.u0" 0) ([])) (Atom "BinPos.Pos.iter_succ_r.u0" 0))
    ((:) (Clause ((:) (Atom "BinPos.Pos.iter_succ.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_succ_r.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter.u0" 0) ([])) (Atom "BinPos.Pos.iter_succ_r.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "BinPos.Pos.iter_add.u0" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_add.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_succ.u0" 0) ([])) (Atom "BinPos.Pos.iter_add.u0" 0))
    ((:) (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_add.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_succ.u0" 0) ([])) (Atom "BinPos.Pos.iter_ind.u0" 0))
    ((:) (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_ind.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter_ind.u0" 0) ([])) (Atom "BinPos.Pos.iter_invariant.u0"
    0)) ((:) (Clause ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_invariant.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "BinPos.Pos.iter_op_succ.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "BinPos.Pos.iter_op_succ.u0" 0)) ((:)
    (Clause ((:) (Atom "BinPos.Pos.iter_op.u0" 0) ([])) (Atom
    "BinPos.Pos.iter_op_succ.u0" 0)) ((:) (Clause ((:) (Atom "Fin.case0.u1"
    0) ([])) (Atom "Fin.case0.u0" 0)) ((:) (Clause ((:) (Atom "Fin.caseS'.u0"
    0) ([])) (Atom "Fin.caseS.u0" 0)) ((:) (Clause ((:) (Atom "Fin.case0.u0"
    0) ([])) (Atom "Fin.rectS.u0" 0)) ((:) (Clause ((:) (Atom "Fin.rectS.u1"
    0) ([])) (Atom "Fin.rectS.u0" 0)) ((:) (Clause ((:) (Atom "Fin.caseS'.u0"
    0) ([])) (Atom "Fin.rect2.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Setoid.Seq_refl.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom "Setoid.Seq_sym.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0)
    ([])) (Atom "Setoid.Seq_trans.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.4" 0)) ((:) (Clause ((:) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.3" 0) ([])) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.4" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Coq.Numbers.Natural.Abstract.NAxioms.6" 0)) ((:)
    (Clause ((:) (Atom "Coq.Numbers.Natural.Abstract.NAxioms.3" 0) ([]))
    (Atom "Coq.Numbers.Natural.Abstract.NAxioms.6" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.8" 0)) ((:) (Clause ((:) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.3" 0) ([])) (Atom
    "Coq.Numbers.Natural.Abstract.NAxioms.8" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.11" 0) ([])) (Atom "recursion.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "recursion_wd.u0" 0)) ((:) (Clause ((:) (Atom "recursion.u0" 0) ([]))
    (Atom "recursion_wd.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "recursion_0.u0" 0)) ((:) (Clause ((:) (Atom "recursion.u0" 0)
    ([])) (Atom "recursion_0.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom "recursion_succ.u0"
    0)) ((:) (Clause ((:) (Atom "recursion.u0" 0) ([])) (Atom
    "recursion_succ.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Coq.Vectors.VectorEq.1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10"
    0) ([])) (Atom "Coq.Vectors.VectorEq.1" 0)) ((:) (Clause ((:) (Atom
    "Vector.eqb_eq.u0" 0) ([])) (Atom "Coq.Vectors.VectorEq.1" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Coq.Vectors.VectorEq.1"
    0)) ((:) (Clause ((:) (Atom "Vector.rect2.u0" 0) ([])) (Atom
    "Coq.Vectors.VectorEq.1" 0)) ((:) (Clause ((:) (Atom "Vector.rect2.u1" 0)
    ([])) (Atom "Coq.Vectors.VectorEq.1" 0)) ((:) (Clause ((:) (Atom
    "Vector.cons_inj.u0" 0) ([])) (Atom "Coq.Vectors.VectorEq.1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.2" 0) ([])) (Atom "Vector.cast.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.cast.u0" 0))
    ((:) (Clause ((:) (Atom "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom
    "ssrunder.Under_rel.Under_rel_from_rel.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "ssrunder.Under_rel.Under_relE.u0" 0)) ((:)
    (Clause ((:) (Atom "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom
    "ssrunder.Under_rel.Under_relE.u0" 0)) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom
    "ssrunder.Under_rel.over_rel.u0" 0)) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom
    "ssrunder.Under_rel.over_rel_done.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.ssr.ssrclasses.1" 0) ([])) (Atom
    "ssrunder.Under_rel.over_rel_done.u0" 0)) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom
    "ssrunder.Under_rel.under_rel_done.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.ssr.ssrclasses.1" 0) ([])) (Atom
    "ssrunder.Under_rel.under_rel_done.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.iter.u0" 0) ([])) (Atom "BinNat.N.iter.u0" 0)) ((:) (Clause
    ((:) (Atom "BinPos.Pos.iter.u0" 0) ([])) (Atom "BinInt.Z.iter.u0" 0))
    ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "option_map.u0" 0))
    ((:) (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "option_map.u1" 0))
    ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom "Coq.Init.Datatypes.26"
    0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "Coq.Init.Datatypes.27" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "surjective_pairing.u0" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0)
    ([])) (Atom "surjective_pairing.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.26" 0) ([])) (Atom "surjective_pairing.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "surjective_pairing.u1" 0))
    ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "surjective_pairing.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.27" 0) ([])) (Atom
    "surjective_pairing.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "injective_projections.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "injective_projections.u0" 0)) ((:) (Clause
    ((:) (Atom "prod.u0" 0) ([])) (Atom "injective_projections.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Datatypes.26" 0) ([])) (Atom
    "injective_projections.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "injective_projections.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "injective_projections.u1" 0)) ((:) (Clause
    ((:) (Atom "prod.u1" 0) ([])) (Atom "injective_projections.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Datatypes.27" 0) ([])) (Atom
    "injective_projections.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "pair_equal_spec.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "pair_equal_spec.u0" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0)
    ([])) (Atom "pair_equal_spec.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.26" 0) ([])) (Atom "pair_equal_spec.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "pair_equal_spec.u1" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "pair_equal_spec.u1" 0))
    ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "pair_equal_spec.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.27" 0) ([])) (Atom
    "pair_equal_spec.u1" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "curry.u0" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "curry.u1" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "uncurry.u0" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "uncurry.u1" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "prod_uncurry_subdef.u0" 0)) ((:) (Clause ((:) (Atom "curry.u0" 0) ([]))
    (Atom "prod_uncurry_subdef.u0" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0)
    ([])) (Atom "prod_uncurry_subdef.u1" 0)) ((:) (Clause ((:) (Atom
    "curry.u1" 0) ([])) (Atom "prod_uncurry_subdef.u1" 0)) ((:) (Clause ((:)
    (Atom "curry.u2" 0) ([])) (Atom "prod_uncurry_subdef.u2" 0)) ((:) (Clause
    ((:) (Atom "prod.u0" 0) ([])) (Atom "prod_curry_subdef.u0" 0)) ((:)
    (Clause ((:) (Atom "uncurry.u0" 0) ([])) (Atom "prod_curry_subdef.u0" 0))
    ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "prod_curry_subdef.u1"
    0)) ((:) (Clause ((:) (Atom "uncurry.u1" 0) ([])) (Atom
    "prod_curry_subdef.u1" 0)) ((:) (Clause ((:) (Atom "uncurry.u2" 0) ([]))
    (Atom "prod_curry_subdef.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "rew_pair.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_pair.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "rew_pair.u1" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "rew_pair.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "rew_pair.u2" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([]))
    (Atom "rew_pair.u2" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "rew_pair.u2" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "length.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "app.u0"
    0)) ((:) (Clause ((:) (Atom "CompSpec.u0" 0) ([])) (Atom
    "CompSpec2Type.u0" 0)) ((:) (Clause ((:) (Atom "CompSpecT.u0" 0) ([]))
    (Atom "CompSpec2Type.u0" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([]))
    (Atom "Decidable.dec_functional_relation.u1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Decidable.dec_functional_relation.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Decidable.dec_functional_relation.u1" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Decidable.dec_functional_relation.u1" 0))
    ((:) (Clause ((:) (Atom "unique.u0" 0) ([])) (Atom
    "Decidable.dec_functional_relation.u1" 0)) ((:) (Clause ((:) (Atom
    "ex.u0" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.1" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Eqdep_dec.eq_proofs_unicity.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.1" 0) ([])) (Atom "Eqdep_dec.eq_proofs_unicity.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Eqdep_dec.K_dec.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.Eqdep_dec.1" 0) ([])) (Atom
    "Eqdep_dec.K_dec.u0" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom
    "Eqdep_dec.inj_right_pair.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Eqdep_dec.inj_right_pair.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.1" 0) ([])) (Atom "Eqdep_dec.inj_right_pair.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Eqdep_dec.K_dec_type.u0"
    0)) ((:) (Clause ((:) (Atom "Eqdep_dec.K_dec.u0" 0) ([])) (Atom
    "Eqdep_dec.K_dec_type.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Eqdep_dec.eq_rect_eq_dec.u0" 0)) ((:) (Clause ((:) (Atom
    "Eqdep_dec.K_dec_type.u0" 0) ([])) (Atom "Eqdep_dec.eq_rect_eq_dec.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom
    "Eqdep_dec.eq_rect_eq_dec.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Eqdep_dec.eq_rect_eq_dec.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "Eqdep_dec.eq_rect_eq_dec.u1" 0)) ((:)
    (Clause ((:) (Atom "EqdepFacts.Eq_rect_eq_on.u0" 0) ([])) (Atom
    "Eqdep_dec.eq_rect_eq_dec.u1" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Streicher_K_on__eq_rect_eq_on.u0" 0) ([])) (Atom
    "Eqdep_dec.eq_rect_eq_dec.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Eqdep_dec.eq_dep_eq_dec.u0" 0)) ((:) (Clause ((:) (Atom
    "Eqdep_dec.eq_rect_eq_dec.u0" 0) ([])) (Atom "Eqdep_dec.eq_dep_eq_dec.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom
    "Eqdep_dec.eq_dep_eq_dec.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom "Eqdep_dec.eq_dep_eq_dec.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Eqdep_dec.UIP_dec.u0" 0))
    ((:) (Clause ((:) (Atom "Eqdep_dec.eq_dep_eq_dec.u0" 0) ([])) (Atom
    "Eqdep_dec.UIP_dec.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom "Eqdep_dec.UIP_dec.u0" 0)) ((:)
    (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.14" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.14"
    0)) ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.14" 0)) ((:) (Clause ((:) (Atom
    "Eqdep_dec.inj_right_pair.u0" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.14" 0))
    ((:) (Clause ((:) (Atom "Eqdep_dec.K_dec_type.u0" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.14" 0)) ((:) (Clause ((:) (Atom
    "Eqdep_dec.eq_rect_eq_dec.u0" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.14" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.14" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom "Coq.Logic.Eqdep_dec.14" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.71" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.14" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Eqdep_dec.inj_pair2_eq_dec.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "Eqdep_dec.inj_pair2_eq_dec.u0" 0)) ((:) (Clause
    ((:) (Atom "Eqdep_dec.eq_rect_eq_dec.u0" 0) ([])) (Atom
    "Eqdep_dec.inj_pair2_eq_dec.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom "Eqdep_dec.inj_pair2_eq_dec.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.71" 0) ([])) (Atom
    "Eqdep_dec.inj_pair2_eq_dec.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Classes.Morphisms.31" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Classes.Morphisms.31" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.Classes.Morphisms.31" 0)) ((:) (Clause
    ((:) (Atom "Basics.compose.u0" 0) ([])) (Atom "Coq.Classes.Morphisms.31"
    0)) ((:) (Clause ((:) (Atom "Basics.compose.u1" 0) ([])) (Atom
    "Coq.Classes.Morphisms.31" 0)) ((:) (Clause ((:) (Atom
    "Basics.compose.u2" 0) ([])) (Atom "Coq.Classes.Morphisms.31" 0)) ((:)
    (Clause ((:) (Atom "Basics.flip.u0" 0) ([])) (Atom
    "Coq.Classes.Morphisms.31" 0)) ((:) (Clause ((:) (Atom "Basics.flip.u1"
    0) ([])) (Atom "Coq.Classes.Morphisms.31" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u2" 0) ([])) (Atom "Coq.Classes.Morphisms.31" 0)) ((:)
    (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_proper.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Morphisms.proper_proper.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Classes.Morphisms.76" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Classes.Morphisms.76" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Coq.Classes.Morphisms.76" 0)) ((:)
    (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Coq.Classes.Morphisms.76" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.proper_proper.u0" 0) ([])) (Atom "Coq.Classes.Morphisms.76"
    0)) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0)
    ([])) (Atom "Morphisms.flip_arrow.u0" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Morphisms.flip_arrow.u0" 0)) ((:)
    (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Morphisms.flip_arrow.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.76" 0) ([])) (Atom "Morphisms.flip_arrow.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([]))
    (Atom "Morphisms.flip_arrow.u1" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Morphisms.flip_arrow.u1" 0)) ((:)
    (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Morphisms.flip_arrow.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.76" 0) ([])) (Atom "Morphisms.flip_arrow.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([]))
    (Atom "Morphisms.proper_sym_flip.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_sym_flip.u1" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Morphisms.proper_sym_flip.u1" 0)) ((:)
    (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Morphisms.proper_sym_flip.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_sym_flip_2.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_sym_flip_2.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_sym_flip_2.u2" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Morphisms.proper_sym_flip_2.u2" 0)) ((:)
    (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Morphisms.proper_sym_flip_2.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_sym_impl_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_sym_impl_iff_2.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.PartialOrder_proper.u0" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Morphisms.PartialOrder_proper.u0" 0))
    ((:) (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Morphisms.PartialOrder_proper.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff_2.u0" 0) ([])) (Atom
    "Morphisms.PartialOrder_proper.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff_2.u1" 0) ([])) (Atom
    "Morphisms.PartialOrder_proper.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.PartialOrder_StrictOrder.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Morphisms.PartialOrder_StrictOrder.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.PartialOrder_proper.u0" 0) ([])) (Atom
    "Morphisms.PartialOrder_StrictOrder.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.StrictOrder_PreOrder.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Morphisms.StrictOrder_PreOrder.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.StrictOrder_PartialOrder.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.StrictOrder_PreOrder.u0" 0) ([])) (Atom
    "Morphisms.StrictOrder_PartialOrder.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.rectS.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.rectS.u2" 0) ([])) (Atom "Vector.rectS.u1" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.case0.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.case0.u2" 0) ([])) (Atom "Vector.case0.u1" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.caseS.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.caseS.u2" 0) ([])) (Atom
    "Vector.caseS.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.caseS'.u0" 0)) ((:) (Clause ((:) (Atom "Vector.caseS'.u2"
    0) ([])) (Atom "Vector.caseS'.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.rect2.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.rect2.u1" 0)) ((:) (Clause
    ((:) (Atom "Vector.case0.u0" 0) ([])) (Atom "Vector.rect2.u1" 0)) ((:)
    (Clause ((:) (Atom "Vector.caseS'.u0" 0) ([])) (Atom "Vector.rect2.u1"
    0)) ((:) (Clause ((:) (Atom "Vector.case0.u1" 0) ([])) (Atom
    "Vector.rect2.u2" 0)) ((:) (Clause ((:) (Atom "Vector.caseS'.u1" 0) ([]))
    (Atom "Vector.rect2.u2" 0)) ((:) (Clause ((:) (Atom "Vector.caseS.u0" 0)
    ([])) (Atom "Vector.hd.u0" 0)) ((:) (Clause ((:) (Atom "Vector.caseS.u1"
    0) ([])) (Atom "Vector.hd.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.rectS.u0" 0) ([])) (Atom "Vector.last.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.rectS.u1" 0) ([])) (Atom "Vector.last.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Datatypes.11" 0) ([])) (Atom "Vector.const.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.const.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.nth.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.caseS.u0" 0) ([])) (Atom
    "Vector.nth.u0" 0)) ((:) (Clause ((:) (Atom "Vector.caseS.u1" 0) ([]))
    (Atom "Vector.nth.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.nth_order.u0" 0)) ((:) (Clause ((:) (Atom "Vector.nth.u0"
    0) ([])) (Atom "Vector.nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.replace.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.caseS'.u0" 0) ([])) (Atom "Vector.replace.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.caseS'.u1" 0) ([])) (Atom "Vector.replace.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.replace_order.u0" 0)) ((:) (Clause ((:) (Atom "Vector.replace.u0"
    0) ([])) (Atom "Vector.replace_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.tl.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.caseS.u0" 0) ([])) (Atom "Vector.tl.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.caseS.u1" 0) ([])) (Atom "Vector.tl.u0" 0)) ((:) (Clause
    ((:) (Atom "prod.u0" 0) ([])) (Atom "Vector.uncons.u0" 0)) ((:) (Clause
    ((:) (Atom "prod.u1" 0) ([])) (Atom "Vector.uncons.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.uncons.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.hd.u0" 0) ([])) (Atom "Vector.uncons.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom "Vector.uncons.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.shiftout.u0" 0)) ((:) (Clause ((:) (Atom "Vector.rectS.u0" 0)
    ([])) (Atom "Vector.shiftout.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.rectS.u1" 0) ([])) (Atom "Vector.shiftout.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.shiftin.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.shiftrepeat.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.rectS.u0" 0) ([])) (Atom
    "Vector.shiftrepeat.u0" 0)) ((:) (Clause ((:) (Atom "Vector.rectS.u1" 0)
    ([])) (Atom "Vector.shiftrepeat.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.2" 0) ([])) (Atom "Vector.take.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.take.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.9" 0) ([])) (Atom "Vector.trunc.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_rect_r.u1" 0) ([])) (Atom "Vector.trunc.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.11" 0) ([])) (Atom
    "Vector.trunc.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.trunc.u0" 0)) ((:) (Clause ((:) (Atom "Vector.shiftout.u0"
    0) ([])) (Atom "Vector.trunc.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.append.u0" 0)) ((:) (Clause ((:)
    (Atom "prod.u0" 0) ([])) (Atom "Vector.splitat.u0" 0)) ((:) (Clause ((:)
    (Atom "prod.u1" 0) ([])) (Atom "Vector.splitat.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.splitat.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.hd.u0" 0) ([])) (Atom "Vector.splitat.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom "Vector.splitat.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.rev_append_tail.u0" 0)) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0)
    ([])) (Atom "Vector.rev_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.rev_append.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.rev_append_tail.u0" 0) ([])) (Atom "Vector.rev_append.u0"
    0)) ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([])) (Atom "Vector.rev.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.rev.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.rev_append.u0" 0) ([])) (Atom
    "Vector.rev.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.map.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.map.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.map2.u0" 0)) ((:) (Clause ((:) (Atom "Vector.rect2.u0" 0) ([]))
    (Atom "Vector.map2.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.map2.u1" 0)) ((:) (Clause ((:) (Atom "Vector.rect2.u1" 0)
    ([])) (Atom "Vector.map2.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.map2.u2" 0)) ((:) (Clause ((:) (Atom
    "Vector.rect2.u2" 0) ([])) (Atom "Vector.map2.u2" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.fold_left.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.fold_right.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.rect2.u0" 0) ([])) (Atom
    "Vector.fold_right2.u0" 0)) ((:) (Clause ((:) (Atom "Vector.rect2.u1" 0)
    ([])) (Atom "Vector.fold_right2.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.rect2.u2" 0) ([])) (Atom "Vector.fold_right2.u2" 0)) ((:) (Clause
    ((:) (Atom "Vector.case0.u1" 0) ([])) (Atom "Vector.fold_left2.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.caseS'.u1" 0) ([])) (Atom
    "Vector.fold_left2.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.fold_left2.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.fold_left2.u2" 0)) ((:) (Clause ((:) (Atom
    "Vector.case0.u0" 0) ([])) (Atom "Vector.fold_left2.u2" 0)) ((:) (Clause
    ((:) (Atom "Vector.caseS'.u0" 0) ([])) (Atom "Vector.fold_left2.u2" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.Forall.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.Exists.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.In.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.Forall2.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.Forall2.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0"
    0) ([])) (Atom "Vector.Exists2.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.Exists2.u1" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Vector.of_list.u0" 0)) ((:) (Clause ((:)
    (Atom "length.u0" 0) ([])) (Atom "Vector.of_list.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.of_list.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Vector.to_list.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.to_list.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.fold_right.u0" 0) ([])) (Atom
    "Vector.to_list.u0" 0)) ((:) (Clause ((:) (Atom "Vector.fold_right.u1" 0)
    ([])) (Atom "Vector.to_list.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.micromega.Env.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.micromega.Env.1" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.micromega.Env.1" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.49" 0) ([])) (Atom
    "Coq.micromega.Env.1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Refl.make_impl.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Refl.make_impl_true.u0" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_impl.u0" 0) ([])) (Atom "Refl.make_impl_true.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "Refl.make_impl_map.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.278"
    0) ([])) (Atom "Refl.make_impl_map.u0" 0)) ((:) (Clause ((:) (Atom
    "prod.u0" 0) ([])) (Atom "Refl.make_impl_map.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Datatypes.26" 0) ([])) (Atom "Refl.make_impl_map.u0" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Refl.make_impl_map.u0"
    0)) ((:) (Clause ((:) (Atom "Refl.make_impl.u0" 0) ([])) (Atom
    "Refl.make_impl_map.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277"
    0) ([])) (Atom "Refl.make_impl_map.u1" 0)) ((:) (Clause ((:) (Atom
    "prod.u1" 0) ([])) (Atom "Refl.make_impl_map.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Datatypes.27" 0) ([])) (Atom "Refl.make_impl_map.u1" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Refl.make_impl_map.u1"
    0)) ((:) (Clause ((:) (Atom "Refl.make_impl.u0" 0) ([])) (Atom
    "Refl.make_impl_map.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Refl.make_conj.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Refl.make_conj_cons.u0" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj.u0" 0) ([])) (Atom "Refl.make_conj_cons.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Refl.make_conj_impl.u0" 0))
    ((:) (Clause ((:) (Atom "Refl.make_impl.u0" 0) ([])) (Atom
    "Refl.make_conj_impl.u0" 0)) ((:) (Clause ((:) (Atom "Refl.make_conj.u0"
    0) ([])) (Atom "Refl.make_conj_impl.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "Refl.make_conj_in.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Refl.make_conj_in.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Refl.make_conj_in.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Refl.make_conj_in.u0" 0))
    ((:) (Clause ((:) (Atom "Refl.make_conj.u0" 0) ([])) (Atom
    "Refl.make_conj_in.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Refl.make_conj_app.u0" 0)) ((:) (Clause ((:) (Atom "app.u0" 0)
    ([])) (Atom "Refl.make_conj_app.u0" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj.u0" 0) ([])) (Atom "Refl.make_conj_app.u0" 0)) ((:)
    (Clause ((:) (Atom "Refl.make_conj_cons.u0" 0) ([])) (Atom
    "Refl.make_conj_app.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247"
    0) ([])) (Atom "Refl.make_conj_rapp.u0" 0)) ((:) (Clause ((:) (Atom
    "list.u0" 0) ([])) (Atom "Refl.make_conj_rapp.u0" 0)) ((:) (Clause ((:)
    (Atom "app.u0" 0) ([])) (Atom "Refl.make_conj_rapp.u0" 0)) ((:) (Clause
    ((:) (Atom "Refl.make_conj.u0" 0) ([])) (Atom "Refl.make_conj_rapp.u0"
    0)) ((:) (Clause ((:) (Atom "Refl.make_conj_cons.u0" 0) ([])) (Atom
    "Refl.make_conj_rapp.u0" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj_app.u0" 0) ([])) (Atom "Refl.make_conj_rapp.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Refl.not_make_conj_cons.u0"
    0)) ((:) (Clause ((:) (Atom "Refl.make_conj.u0" 0) ([])) (Atom
    "Refl.not_make_conj_cons.u0" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj_cons.u0" 0) ([])) (Atom "Refl.not_make_conj_cons.u0" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Refl.not_make_conj_app.u0" 0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([]))
    (Atom "Refl.not_make_conj_app.u0" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj.u0" 0) ([])) (Atom "Refl.not_make_conj_app.u0" 0)) ((:)
    (Clause ((:) (Atom "Refl.not_make_conj_cons.u0" 0) ([])) (Atom
    "Refl.not_make_conj_app.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.micromega.Tauto.8" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.micromega.Tauto.8" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.micromega.Tauto.8"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.9" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10"
    0) ([])) (Atom "Coq.micromega.Tauto.9" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.micromega.Tauto.9" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.micromega.Tauto.10" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.micromega.Tauto.10" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.10" 0)) ((:) (Clause ((:) (Atom
    "list.u0" 0) ([])) (Atom "Coq.micromega.Tauto.10" 0)) ((:) (Clause ((:)
    (Atom "app.u0" 0) ([])) (Atom "Coq.micromega.Tauto.10" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.micromega.Tauto.11" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.micromega.Tauto.11" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.11" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "Coq.micromega.Tauto.11" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "Coq.micromega.Tauto.11" 0)) ((:) (Clause
    ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([]))
    (Atom "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Tauto.rtyp.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.9" 0) ([])) (Atom "Tauto.rtyp.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.38" 0) ([])) (Atom
    "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0" 0) ([]))
    (Atom "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.66" 0) ([])) (Atom "Tauto.rtyp.u0" 0)) ((:) (Clause
    ((:) (Atom "Tauto.is_bool.u0" 0) ([])) (Atom "Tauto.rtyp.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.is_bool_inv.u0" 0) ([])) (Atom "Tauto.rtyp.u0"
    0)) ((:) (Clause ((:) (Atom "Tauto.xcnf.u0" 0) ([])) (Atom
    "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.148" 0)
    ([])) (Atom "Tauto.rtyp.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.8" 0) ([])) (Atom "Tauto.BFormula.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.8" 0) ([])) (Atom
    "Coq.micromega.Tauto.36" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.8" 0) ([])) (Atom "Coq.micromega.Tauto.37" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.9" 0) ([])) (Atom
    "Coq.micromega.Tauto.38" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.10" 0) ([])) (Atom "Coq.micromega.Tauto.39" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.11" 0) ([])) (Atom
    "Coq.micromega.Tauto.40" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.277"
    0) ([])) (Atom "Tauto.map_simpl.u0" 0)) ((:) (Clause ((:) (Atom "list.u0"
    0) ([])) (Atom "Tauto.map_simpl.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "Tauto.map_simpl.u1" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Tauto.map_simpl.u1" 0)) ((:) (Clause
    ((:) (Atom "list.u0" 0) ([])) (Atom "Tauto.map_simpl.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.micromega.Tauto.8" 0) ([])) (Atom
    "Coq.micromega.Tauto.50" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247"
    0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.277" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.377" 0) ([])) (Atom
    "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.378"
    0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([]))
    (Atom "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom "sum.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom
    "prod.u0" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Datatypes.26" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.micromega.Tauto.51"
    0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom "Refl.make_impl.u0"
    0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj.u0" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:)
    (Clause ((:) (Atom "Refl.make_conj_cons.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj_impl.u0" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:)
    (Clause ((:) (Atom "Refl.make_conj_app.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj_rapp.u0" 0) ([])) (Atom "Coq.micromega.Tauto.51" 0)) ((:)
    (Clause ((:) (Atom "Tauto.if_same.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.51" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247"
    0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.277" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom
    "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.377"
    0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.378" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:)
    (Atom "sum.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:) (Clause
    ((:) (Atom "sum.u1" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:)
    (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0))
    ((:) (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "Coq.micromega.Tauto.52"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Datatypes.26" 0) ([])) (Atom
    "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.27" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0))
    ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52"
    0)) ((:) (Clause ((:) (Atom "Refl.make_impl.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom "Refl.make_conj.u0"
    0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj_cons.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:)
    (Clause ((:) (Atom "Refl.make_conj_impl.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj_app.u0" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:)
    (Clause ((:) (Atom "Refl.make_conj_rapp.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom "Tauto.Trace.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.10" 0) ([])) (Atom "Coq.micromega.Tauto.52" 0)) ((:)
    (Clause ((:) (Atom "Tauto.if_same.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.52" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.9" 0) ([])) (Atom "Tauto.TFormula.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.11" 0) ([])) (Atom
    "Tauto.TFormula.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.66" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u1" 0) ([])) (Atom "Coq.micromega.Tauto.67" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.9" 0) ([])) (Atom
    "Tauto.is_bool.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0" 0)
    ([])) (Atom "Tauto.is_bool.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.11" 0) ([])) (Atom "Tauto.is_bool.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.TFormula.u1" 0) ([])) (Atom "Tauto.is_bool.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.9" 0) ([])) (Atom
    "Tauto.is_bool_inv.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0" 0)
    ([])) (Atom "Tauto.is_bool_inv.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.is_bool.u0" 0) ([])) (Atom "Tauto.is_bool_inv.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.micromega.Tauto.11" 0) ([])) (Atom "Tauto.is_bool_inv.u1"
    0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u1" 0) ([])) (Atom
    "Tauto.is_bool_inv.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.is_bool.u1" 0)
    ([])) (Atom "Tauto.is_bool_inv.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.9" 0) ([])) (Atom "Tauto.xcnf.u0" 0)) ((:) (Clause
    ((:) (Atom "Tauto.TFormula.u0" 0) ([])) (Atom "Tauto.xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.66" 0) ([])) (Atom
    "Tauto.xcnf.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.is_bool.u0" 0) ([]))
    (Atom "Tauto.xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.11" 0) ([])) (Atom "Tauto.xcnf.u1" 0)) ((:) (Clause
    ((:) (Atom "Tauto.TFormula.u1" 0) ([])) (Atom "Tauto.xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.67" 0) ([])) (Atom
    "Tauto.xcnf.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.is_bool.u1" 0) ([]))
    (Atom "Tauto.xcnf.u1" 0)) ((:) (Clause ((:) (Atom "option.u0" 0) ([]))
    (Atom "Tauto.ocons.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Tauto.ocons.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.126" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u1" 0) ([])) (Atom "Coq.micromega.Tauto.127" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.9" 0) ([])) (Atom
    "Tauto.rxcnf.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0" 0) ([]))
    (Atom "Tauto.rxcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.126" 0) ([])) (Atom "Tauto.rxcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.micromega.Tauto.11" 0) ([])) (Atom
    "Tauto.rxcnf.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u1" 0) ([]))
    (Atom "Tauto.rxcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.127" 0) ([])) (Atom "Tauto.rxcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "ex.u0" 0) ([])) (Atom "Coq.micromega.Tauto.148" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.micromega.Tauto.148"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.micromega.Tauto.148" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.148" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "Coq.micromega.Tauto.148" 0)) ((:) (Clause
    ((:) (Atom "Coq.micromega.Tauto.9" 0) ([])) (Atom
    "Coq.micromega.Tauto.148" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0"
    0) ([])) (Atom "Coq.micromega.Tauto.148" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.66" 0) ([])) (Atom "Coq.micromega.Tauto.148" 0))
    ((:) (Clause ((:) (Atom "Tauto.is_bool.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.148" 0)) ((:) (Clause ((:) (Atom
    "Tauto.is_bool_inv.u0" 0) ([])) (Atom "Coq.micromega.Tauto.148" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u0" 0) ([])) (Atom
    "Coq.micromega.Tauto.148" 0)) ((:) (Clause ((:) (Atom "option.u0" 0)
    ([])) (Atom "Coq.micromega.Tauto.149" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.11" 0) ([])) (Atom "Coq.micromega.Tauto.149" 0))
    ((:) (Clause ((:) (Atom "Tauto.TFormula.u1" 0) ([])) (Atom
    "Coq.micromega.Tauto.149" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.67" 0) ([])) (Atom "Coq.micromega.Tauto.149" 0))
    ((:) (Clause ((:) (Atom "Tauto.is_bool.u1" 0) ([])) (Atom
    "Coq.micromega.Tauto.149" 0)) ((:) (Clause ((:) (Atom
    "Tauto.is_bool_inv.u1" 0) ([])) (Atom "Coq.micromega.Tauto.149" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u1" 0) ([])) (Atom
    "Coq.micromega.Tauto.149" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Tauto.if_same.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Tauto.if_same.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u0" 0) ([])) (Atom "Tauto.rxcnf_and_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u0" 0) ([])) (Atom
    "Tauto.rxcnf_and_xcnf.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u0" 0)
    ([])) (Atom "Tauto.rxcnf_and_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u1" 0) ([])) (Atom "Tauto.rxcnf_and_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u1" 0) ([])) (Atom
    "Tauto.rxcnf_and_xcnf.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u1" 0)
    ([])) (Atom "Tauto.rxcnf_and_xcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u0" 0) ([])) (Atom "Tauto.rxcnf_or_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u0" 0) ([])) (Atom
    "Tauto.rxcnf_or_xcnf.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u0" 0)
    ([])) (Atom "Tauto.rxcnf_or_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u1" 0) ([])) (Atom "Tauto.rxcnf_or_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u1" 0) ([])) (Atom
    "Tauto.rxcnf_or_xcnf.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u1" 0)
    ([])) (Atom "Tauto.rxcnf_or_xcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u0" 0) ([])) (Atom "Tauto.rxcnf_impl_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u0" 0) ([])) (Atom
    "Tauto.rxcnf_impl_xcnf.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u0"
    0) ([])) (Atom "Tauto.rxcnf_impl_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u1" 0) ([])) (Atom "Tauto.rxcnf_impl_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u1" 0) ([])) (Atom
    "Tauto.rxcnf_impl_xcnf.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u1"
    0) ([])) (Atom "Tauto.rxcnf_impl_xcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u0" 0) ([])) (Atom "Tauto.rxcnf_iff_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u0" 0) ([])) (Atom
    "Tauto.rxcnf_iff_xcnf.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u0" 0)
    ([])) (Atom "Tauto.rxcnf_iff_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.TFormula.u1" 0) ([])) (Atom "Tauto.rxcnf_iff_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.xcnf.u1" 0) ([])) (Atom
    "Tauto.rxcnf_iff_xcnf.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.rxcnf.u1" 0)
    ([])) (Atom "Tauto.rxcnf_iff_xcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.9" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.TFormula.u0" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.xcnf.u0" 0)
    ([])) (Atom "Tauto.rxcnf_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.126" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf.u0" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.148" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_and_xcnf.u0" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf_or_xcnf.u0" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_impl_xcnf.u0" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf_iff_xcnf.u0" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.11" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.TFormula.u1" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u1" 0)) ((:) (Clause ((:) (Atom "Tauto.xcnf.u1" 0)
    ([])) (Atom "Tauto.rxcnf_xcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.127" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf.u1" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.149" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_and_xcnf.u1" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf_or_xcnf.u1" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u1" 0)) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf_impl_xcnf.u1" 0) ([])) (Atom "Tauto.rxcnf_xcnf.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.rxcnf_iff_xcnf.u1" 0) ([])) (Atom
    "Tauto.rxcnf_xcnf.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Coq.micromega.Tauto.324" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.8" 0) ([])) (Atom "Tauto.eval_bf.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.BFormula.u0" 0) ([])) (Atom "Tauto.eval_bf.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.8" 0) ([])) (Atom
    "Tauto.eval_bf_map.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.BFormula.u0" 0)
    ([])) (Atom "Tauto.eval_bf_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.36" 0) ([])) (Atom "Tauto.eval_bf_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Tauto.eval_bf.u0" 0) ([])) (Atom
    "Tauto.eval_bf_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.37" 0) ([])) (Atom "Tauto.eval_bf_map.u1" 0)) ((:)
    (Clause ((:) (Atom "Tauto.eval_bf.u0" 0) ([])) (Atom
    "Tauto.eval_bf_map.u1" 0)) ((:) (Clause ((:) (Atom "VarMap.t.u0" 0) ([]))
    (Atom "Coq.micromega.VarMap.5" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.micromega.ZCoeff.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.1" 0) ([])) (Atom "Coq.micromega.ZCoeff.1"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.OrderedRing.1" 0) ([])) (Atom
    "Coq.micromega.ZCoeff.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.OrderedRing.21" 0) ([])) (Atom "Coq.micromega.ZCoeff.1"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.RingMicromega.1" 0) ([]))
    (Atom "Coq.micromega.ZCoeff.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.micromega.ZCoeff.1" 0))
    ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.micromega.ZCoeff.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom "Coq.micromega.ZCoeff.1"
    0)) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0)
    ([])) (Atom "Coq.micromega.EnvRing.9" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Coq.micromega.EnvRing.9" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.micromega.EnvRing.9" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.9"
    0)) ((:) (Clause ((:) (Atom "Setoid.Seq_refl.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.9" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.micromega.EnvRing.9" 0))
    ((:) (Clause ((:) (Atom "Coq.micromega.Env.1" 0) ([])) (Atom
    "Coq.micromega.EnvRing.9" 0)) ((:) (Clause ((:) (Atom
    "EnvRing.env_morph.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.9" 0)) ((:)
    (Clause ((:) (Atom "EnvRing.Pjump_add.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.9" 0)) ((:) (Clause ((:) (Atom
    "EnvRing.Mphi_morph.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.9" 0)) ((:)
    (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.micromega.EnvRing.9" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom "Coq.micromega.EnvRing.9"
    0)) ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.100" 0) ([]))
    (Atom "Coq.micromega.EnvRing.9" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.map_option.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.10"
    0)) ((:) (Clause ((:) (Atom "RingMicromega.map_option.u1" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.map_option2.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.10"
    0)) ((:) (Clause ((:) (Atom "RingMicromega.map_option2.u1" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "RingMicromega.map_option2.u2" 0) ([])) (Atom "Coq.micromega.EnvRing.10"
    0)) ((:) (Clause ((:) (Atom "RingMicromega.Formula.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Wf.1" 0)
    ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.13" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.44" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.278" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.378" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.381" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.382" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom "ex.u0" 0) ([]))
    (Atom "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Arith.Wf_nat.1" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "option.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.10"
    0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([]))
    (Atom "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.26" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([]))
    (Atom "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_impl.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "Refl.make_impl_map.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "Refl.make_conj_cons.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Refl.make_conj_impl.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0))
    ((:) (Clause ((:) (Atom "Refl.make_conj_in.u0" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.51" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0))
    ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.324" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom "EnvRing.PExpr.u0"
    0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "EnvRing.Pol.u0" 0) ([])) (Atom "Coq.micromega.EnvRing.10" 0)) ((:)
    (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.97" 0) ([])) (Atom
    "Coq.micromega.EnvRing.11" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "ssrsetoid.compat_Reflexive.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.ssr.ssrclasses.1" 0) ([])) (Atom "ssrsetoid.compat_Reflexive.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0) ([]))
    (Atom "Relations.inverse_image_of_equivalence.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Relations.inverse_image_of_equivalence.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Relations.inverse_image_of_eq.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Relations.inverse_image_of_eq.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Relations.inverse_image_of_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "Coq.setoid_ring.Ring_polynom.1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.setoid_ring.Ring_polynom.1" 0)) ((:)
    (Clause ((:) (Atom "Setoid.Seq_refl.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "list.u0" 0) ([])) (Atom "Coq.setoid_ring.Ring_polynom.1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.BinList.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Coq.setoid_ring.Ring_polynom.2" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom "option.u0"
    0) ([])) (Atom "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:)
    (Atom "prod.u0" 0) ([])) (Atom "Coq.setoid_ring.Ring_polynom.2" 0)) ((:)
    (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Datatypes.26" 0) ([])) (Atom "Coq.setoid_ring.Ring_polynom.2"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom "app.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.97" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_polynom.3" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.default_relation.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.equivalence_default.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.32" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.70" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Setoid.Seq_refl.u0" 0) ([])) (Atom "Coq.setoid_ring.Field_theory.1" 0))
    ((:) (Clause ((:) (Atom "Setoid.Seq_sym.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Setoid.Seq_trans.u0" 0) ([])) (Atom "Coq.setoid_ring.Field_theory.1" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_polynom.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.BinList.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Field_theory.7" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Coq.setoid_ring.Field_theory.7" 0)) ((:)
    (Clause ((:) (Atom "option.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.7" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Field_theory.7" 0)) ((:) (Clause ((:) (Atom
    "prod.u1" 0) ([])) (Atom "Coq.setoid_ring.Field_theory.7" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.7" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_polynom.2" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.7" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.7" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.7" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_polynom.3" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.97" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.10" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Field_theory.1" 0) ([])) (Atom "Field_theory.SF2AF.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.100" 0) ([]))
    (Atom "Field_theory.SF2AF.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.428" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.428" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.InitialRing.32" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.428" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.428" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Field_theory.1" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.428" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.428" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0) ([])) (Atom
    "Coq.setoid_ring.Field_theory.428" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom "Coq.setoid_ring.Ring_theory.1"
    0)) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_theory.17" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_theory.74" 0)) ((:) (Clause ((:) (Atom
    "option.u0" 0) ([])) (Atom "Coq.setoid_ring.Ring_theory.74" 0)) ((:)
    (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_theory.74" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.default_relation.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.equivalence_default.u0" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.setoid_ring.Ring_theory.100" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.100" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.113" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.120" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.120" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "Coq.setoid_ring.Ring_theory.120" 0)) ((:) (Clause ((:) (Atom
    "Coq.setoid_ring.Ring_theory.17" 0) ([])) (Atom "ring_kind.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.setoid_ring.Ring_theory.74" 0) ([])) (Atom
    "ring_kind.u2" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Zcomplements.Zlength_aux.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.ZArith.Zcomplements.5" 0)) ((:) (Clause ((:) (Atom
    "list.u0" 0) ([])) (Atom "Coq.ZArith.Zcomplements.5" 0)) ((:) (Clause
    ((:) (Atom "length.u0" 0) ([])) (Atom "Coq.ZArith.Zcomplements.5" 0))
    ((:) (Clause ((:) (Atom "Zcomplements.Zlength_aux.u0" 0) ([])) (Atom
    "Coq.ZArith.Zcomplements.5" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Logic.EqdepFacts.1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Coq.Logic.EqdepFacts.2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "Coq.Logic.EqdepFacts.2" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.2"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "EqdepFacts.eq_sigT_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "EqdepFacts.eq_sigT_eq_dep.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "EqdepFacts.eq_sigT_eq_dep.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u1" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "EqdepFacts.eq_sigT_eq_dep.u1" 0)) ((:) (Clause ((:) (Atom
    "sigT.u1" 0) ([])) (Atom "EqdepFacts.eq_sigT_eq_dep.u1" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom "EqdepFacts.eq_sigT_eq_dep.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_dep_eq_sigT.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0)
    ([])) (Atom "EqdepFacts.eq_dep_eq_sigT.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "EqdepFacts.eq_dep_eq_sigT.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_dep_eq_sigT.u1" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0)
    ([])) (Atom "EqdepFacts.eq_dep_eq_sigT.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom "EqdepFacts.eq_dep_eq_sigT.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0"
    0) ([])) (Atom "EqdepFacts.eq_sigT_iff_eq_dep.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_dep_eq_sigT.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "EqdepFacts.eq_sigT_iff_eq_dep.u1" 0)) ((:) (Clause ((:)
    (Atom "sigT.u1" 0) ([])) (Atom "EqdepFacts.eq_sigT_iff_eq_dep.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u1" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u1" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u1" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_dep_eq_sigT.u1" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_iff_eq_dep.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "EqdepFacts.eq_sig_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "EqdepFacts.eq_sig_eq_dep.u0" 0)) ((:)
    (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom "EqdepFacts.eq_sig_eq_dep.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "EqdepFacts.eq_sig_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "EqdepFacts.eq_sig_eq_dep.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_dep_eq_sig.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0)
    ([])) (Atom "EqdepFacts.eq_dep_eq_sig.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "EqdepFacts.eq_dep_eq_sig.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sig_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0)
    ([])) (Atom "EqdepFacts.eq_sig_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "EqdepFacts.eq_sig_iff_eq_dep.u0"
    0)) ((:) (Clause ((:) (Atom "EqdepFacts.eq_sig_eq_dep.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sig_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_dep_eq_sig.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sig_iff_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "EqdepFacts.eq_sigT_sig_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "EqdepFacts.eq_sigT_sig_eq.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Specif.22" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_sig_eq.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "EqdepFacts.eq_sigT_sig_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "EqdepFacts.eq_sigT_sig_eq.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_sig_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "EqdepFacts.eq_sigT_sig_eq.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_fst.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0)
    ([])) (Atom "EqdepFacts.eq_sigT_fst.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "EqdepFacts.eq_sigT_fst.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "EqdepFacts.eq_sigT_fst.u1" 0))
    ((:) (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_fst.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.23" 0) ([])) (Atom "EqdepFacts.eq_sigT_fst.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "EqdepFacts.eq_sigT_snd.u0" 0))
    ((:) (Clause ((:) (Atom "sigT.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_snd.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.22" 0) ([])) (Atom "EqdepFacts.eq_sigT_snd.u0" 0)) ((:)
    (Clause ((:) (Atom "EqdepFacts.eq_sigT_fst.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_snd.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "EqdepFacts.eq_sigT_snd.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "EqdepFacts.eq_sigT_snd.u1" 0)) ((:)
    (Clause ((:) (Atom "sigT.u1" 0) ([])) (Atom "EqdepFacts.eq_sigT_snd.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Specif.23" 0) ([])) (Atom
    "EqdepFacts.eq_sigT_snd.u1" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_fst.u1" 0) ([])) (Atom "EqdepFacts.eq_sigT_snd.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sig_fst.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "EqdepFacts.eq_sig_fst.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "EqdepFacts.eq_sig_fst.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "EqdepFacts.eq_sig_snd.u0" 0))
    ((:) (Clause ((:) (Atom "sig.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sig_snd.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Specif.16" 0) ([])) (Atom "EqdepFacts.eq_sig_snd.u0" 0)) ((:)
    (Clause ((:) (Atom "EqdepFacts.eq_sig_fst.u0" 0) ([])) (Atom
    "EqdepFacts.eq_sig_snd.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Logic.EqdepFacts.46" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "Coq.Logic.EqdepFacts.46" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.Eq_rect_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.9" 0) ([])) (Atom "EqdepFacts.Eq_rect_eq_on.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "EqdepFacts.Eq_dep_eq_on.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom
    "EqdepFacts.Eq_dep_eq_on.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "EqdepFacts.eq_rect_eq_on__eq_dep1_eq_on.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep1_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_rect_eq_on.u0" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep1_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "EqdepFacts.eq_rect_eq__eq_dep1_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq__eq_dep1_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_rect_eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq__eq_dep1_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep1_eq_on.u0" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq__eq_dep1_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_rect_eq_on.u0" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_dep_eq_on.u0" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep1_eq_on.u0" 0) ([])) (Atom
    "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "EqdepFacts.Streicher_K_on__eq_rect_eq_on.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "EqdepFacts.Streicher_K_on__eq_rect_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_rect_eq_on.u0" 0) ([])) (Atom
    "EqdepFacts.Streicher_K_on__eq_rect_eq_on.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "EqdepFacts.UIP_shift_on.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom
    "EqdepFacts.UIP_shift_on.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "EqdepFacts.UIP_shift.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom "EqdepFacts.UIP_shift.u0" 0))
    ((:) (Clause ((:) (Atom "EqdepFacts.UIP_shift_on.u0" 0) ([])) (Atom
    "EqdepFacts.UIP_shift.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Logic.EqdepFacts.71" 0)) ((:) (Clause ((:) (Atom "sigT.u0" 0)
    ([])) (Atom "Coq.Logic.EqdepFacts.71" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.eq_sigT_eq_dep.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.71"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.71" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "EqdepFacts.Inj_dep_pair_on.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u1" 0) ([])) (Atom "EqdepFacts.Inj_dep_pair_on.u0" 0)) ((:) (Clause
    ((:) (Atom "EqdepFacts.eq_sigT_eq_dep.u1" 0) ([])) (Atom
    "EqdepFacts.eq_dep_eq_on__inj_pair2_on.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_dep_eq_on.u0" 0) ([])) (Atom
    "EqdepFacts.eq_dep_eq_on__inj_pair2_on.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Inj_dep_pair_on.u0" 0) ([])) (Atom
    "EqdepFacts.eq_dep_eq_on__inj_pair2_on.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.78" 0)) ((:) (Clause ((:)
    (Atom "eq.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.80" 0)) ((:) (Clause
    ((:) (Atom "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.80" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.46" 0) ([])) (Atom "Coq.Logic.EqdepFacts.80" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.78" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.80" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Logic.EqdepFacts.82" 0)) ((:) (Clause ((:) (Atom
    "Eqdep_dec.eq_rect_eq_dec.u1" 0) ([])) (Atom "Coq.Logic.EqdepFacts.82"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.82" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_dep_eq_on.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.82" 0))
    ((:) (Clause ((:) (Atom "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on.u0" 0)
    ([])) (Atom "Coq.Logic.EqdepFacts.82" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Coq.Logic.EqdepFacts.83" 0)) ((:) (Clause ((:) (Atom
    "sigT.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.83" 0)) ((:) (Clause ((:)
    (Atom "Coq.Logic.EqdepFacts.71" 0) ([])) (Atom "Coq.Logic.EqdepFacts.83"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.80" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.83" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Coq.Logic.EqdepFacts.84" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0)
    ([])) (Atom "Coq.Logic.EqdepFacts.84" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Inj_dep_pair_on.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.84"
    0)) ((:) (Clause ((:) (Atom "EqdepFacts.eq_dep_eq_on__inj_pair2_on.u0" 0)
    ([])) (Atom "Coq.Logic.EqdepFacts.84" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.82" 0) ([])) (Atom "Coq.Logic.EqdepFacts.84" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom
    "EqdepFacts.f_eq_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom "EqdepFacts.f_eq_dep.u1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom
    "EqdepFacts.f_eq_dep.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom "EqdepFacts.eq_dep_non_dep.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.eq_dep_non_dep.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom "EqdepFacts.eq_dep_non_dep.u1"
    0)) ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.1" 0) ([])) (Atom
    "EqdepFacts.f_eq_dep_non_dep.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.2" 0) ([])) (Atom "EqdepFacts.f_eq_dep_non_dep.u1"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "EqdepFacts.f_eq_dep_non_dep.u2" 0)) ((:) (Clause ((:) (Atom
    "identity.u0" 0) ([])) (Atom "Coq.Init.Logic_Type.2" 0)) ((:) (Clause
    ((:) (Atom "identity.u0" 0) ([])) (Atom "identity_ind_r.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic_Type.2" 0) ([])) (Atom
    "identity_ind_r.u0" 0)) ((:) (Clause ((:) (Atom "identity.u0" 0) ([]))
    (Atom "identity_rec_r.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic_Type.2" 0) ([])) (Atom "identity_rec_r.u0" 0)) ((:)
    (Clause ((:) (Atom "identity.u0" 0) ([])) (Atom "identity_rect_r.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic_Type.2" 0) ([])) (Atom
    "identity_rect_r.u0" 0)) ((:) (Clause ((:) (Atom "ZifyClasses.InjTyp.u0"
    0) ([])) (Atom "ZifyClasses.BinOp.u0" 0)) ((:) (Clause ((:) (Atom
    "ZifyClasses.InjTyp.u0" 0) ([])) (Atom "ZifyClasses.BinOp.u1" 0)) ((:)
    (Clause ((:) (Atom "ZifyClasses.InjTyp.u0" 0) ([])) (Atom
    "ZifyClasses.BinOp.u2" 0)) ((:) (Clause ((:) (Atom
    "ZifyClasses.InjTyp.u1" 0) ([])) (Atom "ZifyClasses.BinOp.u3" 0)) ((:)
    (Clause ((:) (Atom "ZifyClasses.InjTyp.u1" 0) ([])) (Atom
    "ZifyClasses.BinOp.u4" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "ZifyClasses.BinOp.u5" 0)) ((:) (Clause ((:) (Atom
    "ZifyClasses.InjTyp.u1" 0) ([])) (Atom "ZifyClasses.BinOp.u5" 0)) ((:)
    (Clause ((:) (Atom "ZifyClasses.InjTyp.u0" 0) ([])) (Atom
    "ZifyClasses.UnOp.u0" 0)) ((:) (Clause ((:) (Atom "ZifyClasses.InjTyp.u0"
    0) ([])) (Atom "ZifyClasses.UnOp.u1" 0)) ((:) (Clause ((:) (Atom
    "ZifyClasses.InjTyp.u1" 0) ([])) (Atom "ZifyClasses.UnOp.u2" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "ZifyClasses.UnOp.u3" 0)) ((:)
    (Clause ((:) (Atom "ZifyClasses.InjTyp.u1" 0) ([])) (Atom
    "ZifyClasses.UnOp.u3" 0)) ((:) (Clause ((:) (Atom "ZifyClasses.InjTyp.u0"
    0) ([])) (Atom "ZifyClasses.CstOp.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "ZifyClasses.CstOp.u1" 0)) ((:) (Clause ((:) (Atom
    "ZifyClasses.InjTyp.u1" 0) ([])) (Atom "ZifyClasses.CstOp.u1" 0)) ((:)
    (Clause ((:) (Atom "ZifyClasses.InjTyp.u0" 0) ([])) (Atom
    "ZifyClasses.BinRel.u0" 0)) ((:) (Clause ((:) (Atom
    "ZifyClasses.InjTyp.u1" 0) ([])) (Atom "ZifyClasses.BinRel.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "ZifyClasses.injterm.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "ZifyClasses.mkapp2.u3"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "ZifyClasses.mkapp2.u4" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "ZifyClasses.mkapp2.u5" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "ZifyClasses.mkapp.u2" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "ZifyClasses.mkapp.u3" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "ZifyClasses.mkrel.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Vector.cons_inj.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.cons_inj.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.caseS.u0" 0) ([])) (Atom "Vector.cons_inj.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.caseS.u1" 0) ([])) (Atom "Vector.cons_inj.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.eta.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.eta.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.caseS.u0" 0) ([])) (Atom "Vector.eta.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.hd.u0" 0) ([])) (Atom "Vector.eta.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom "Vector.eta.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Vector.eq_nth_iff.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.eq_nth_iff.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.rect2.u0" 0) ([])) (Atom "Vector.eq_nth_iff.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.rect2.u1" 0) ([])) (Atom "Vector.eq_nth_iff.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom
    "Vector.eq_nth_iff.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.nth_order_hd.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Vector.nth_order_hd.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.nth_order_hd.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.hd.u0" 0) ([])) (Atom "Vector.nth_order_hd.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.nth_order.u0" 0) ([])) (Atom
    "Vector.nth_order_hd.u0" 0)) ((:) (Clause ((:) (Atom "Vector.eta.u0" 0)
    ([])) (Atom "Vector.nth_order_hd.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Vector.nth_order_tl.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Vector.nth_order_tl.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.nth_order_tl.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom
    "Vector.nth_order_tl.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order.u0" 0) ([])) (Atom "Vector.nth_order_tl.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom "Vector.nth_order_tl.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.eta.u0" 0) ([])) (Atom
    "Vector.nth_order_tl.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Vector.nth_order_last.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.nth_order_last.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.rectS.u0" 0) ([])) (Atom "Vector.nth_order_last.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.last.u0" 0) ([])) (Atom
    "Vector.nth_order_last.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order.u0" 0) ([])) (Atom "Vector.nth_order_last.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.nth_order_ext.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.nth_order_ext.u0" 0)) ((:) (Clause ((:) (Atom "Vector.nth.u0" 0)
    ([])) (Atom "Vector.nth_order_ext.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order.u0" 0) ([])) (Atom "Vector.nth_order_ext.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.shiftin_nth.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.shiftin_nth.u0" 0)) ((:) (Clause ((:) (Atom "Vector.caseS.u0" 0)
    ([])) (Atom "Vector.shiftin_nth.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth.u0" 0) ([])) (Atom "Vector.shiftin_nth.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.shiftin.u0" 0) ([])) (Atom "Vector.shiftin_nth.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.shiftin_last.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.shiftin_last.u0" 0)) ((:) (Clause ((:) (Atom "Vector.last.u0" 0)
    ([])) (Atom "Vector.shiftin_last.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.shiftin.u0" 0) ([])) (Atom "Vector.shiftin_last.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.shiftrepeat_nth.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.shiftrepeat_nth.u0" 0)) ((:) (Clause ((:) (Atom "Vector.rectS.u2"
    0) ([])) (Atom "Vector.shiftrepeat_nth.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.caseS.u0" 0) ([])) (Atom "Vector.shiftrepeat_nth.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom
    "Vector.shiftrepeat_nth.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.shiftrepeat.u0" 0) ([])) (Atom "Vector.shiftrepeat_nth.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.shiftrepeat_last.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.shiftrepeat_last.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.rectS.u0" 0) ([])) (Atom "Vector.shiftrepeat_last.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.last.u0" 0) ([])) (Atom
    "Vector.shiftrepeat_last.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.shiftrepeat.u0" 0) ([])) (Atom "Vector.shiftrepeat_last.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Vector.nth_order_replace_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.hd.u0" 0) ([])) (Atom "Vector.nth_order_replace_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.nth_order.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.replace.u0" 0) ([])) (Atom "Vector.nth_order_replace_eq.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.eta.u0" 0) ([])) (Atom "Vector.nth_order_replace_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.nth_order_hd.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order_tl.u0" 0) ([])) (Atom "Vector.nth_order_replace_eq.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_neq.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Vector.nth_order_replace_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_neq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.hd.u0" 0) ([])) (Atom "Vector.nth_order_replace_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.nth_order.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_neq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.replace.u0" 0) ([])) (Atom "Vector.nth_order_replace_neq.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_neq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.eta.u0" 0) ([])) (Atom "Vector.nth_order_replace_neq.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.nth_order_hd.u0" 0) ([])) (Atom
    "Vector.nth_order_replace_neq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order_tl.u0" 0) ([])) (Atom "Vector.nth_order_replace_neq.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.replace_id.u0"
    0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.replace_id.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.replace_id.u0" 0)) ((:) (Clause ((:) (Atom "Vector.hd.u0"
    0) ([])) (Atom "Vector.replace_id.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth.u0" 0) ([])) (Atom "Vector.replace_id.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.replace.u0" 0) ([])) (Atom "Vector.replace_id.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom
    "Vector.replace_id.u0" 0)) ((:) (Clause ((:) (Atom "Vector.eta.u0" 0)
    ([])) (Atom "Vector.replace_id.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Vector.replace_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Vector.replace_replace_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.replace_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom "Vector.hd.u0"
    0) ([])) (Atom "Vector.replace_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.replace.u0" 0) ([])) (Atom "Vector.replace_replace_eq.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom
    "Vector.replace_replace_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.eta.u0" 0) ([])) (Atom "Vector.replace_replace_eq.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Vector.replace_replace_neq.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0"
    0) ([])) (Atom "Vector.replace_replace_neq.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.rectS.u0" 0) ([])) (Atom "Vector.replace_replace_neq.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.replace.u0" 0) ([])) (Atom
    "Vector.replace_replace_neq.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Vector.const_nth.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.const.u0" 0) ([])) (Atom "Vector.const_nth.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom "Vector.const_nth.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.map_id.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Vector.map_id.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.map_id.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.map.u0" 0) ([])) (Atom
    "Vector.map_id.u0" 0)) ((:) (Clause ((:) (Atom "Vector.map.u1" 0) ([]))
    (Atom "Vector.map_id.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.map_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.map.u0" 0) ([])) (Atom "Vector.map_map.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.map.u0" 0) ([])) (Atom "Vector.map_map.u1" 0)) ((:) (Clause
    ((:) (Atom "Vector.map.u1" 0) ([])) (Atom "Vector.map_map.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.map_map.u2" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Vector.map_map.u2" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.map_map.u2"
    0)) ((:) (Clause ((:) (Atom "Vector.map.u1" 0) ([])) (Atom
    "Vector.map_map.u2" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.map_ext_in.u0" 0)) ((:) (Clause ((:) (Atom "Vector.map.u0"
    0) ([])) (Atom "Vector.map_ext_in.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.In.u0" 0) ([])) (Atom "Vector.map_ext_in.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.map_ext_in.u1" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Vector.map_ext_in.u1" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.map_ext_in.u1"
    0)) ((:) (Clause ((:) (Atom "Vector.map.u1" 0) ([])) (Atom
    "Vector.map_ext_in.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([]))
    (Atom "Vector.map_ext.u0" 0)) ((:) (Clause ((:) (Atom "Vector.map.u0" 0)
    ([])) (Atom "Vector.map_ext.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.map_ext_in.u0" 0) ([])) (Atom "Vector.map_ext.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.map_ext.u1" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.map_ext.u1" 0))
    ((:) (Clause ((:) (Atom "Vector.map.u1" 0) ([])) (Atom
    "Vector.map_ext.u1" 0)) ((:) (Clause ((:) (Atom "Vector.map_ext_in.u1" 0)
    ([])) (Atom "Vector.map_ext.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0"
    0) ([])) (Atom "Vector.nth_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.caseS.u0" 0) ([])) (Atom "Vector.nth_map.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom "Vector.nth_map.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.map.u0" 0) ([])) (Atom "Vector.nth_map.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.nth_map.u1" 0))
    ((:) (Clause ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom
    "Vector.nth_map.u1" 0)) ((:) (Clause ((:) (Atom "Vector.map.u1" 0) ([]))
    (Atom "Vector.nth_map.u1" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.nth_map2.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.rect2.u0" 0) ([])) (Atom "Vector.nth_map2.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom "Vector.nth_map2.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.map2.u0" 0) ([])) (Atom "Vector.nth_map2.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.nth_map2.u1" 0)) ((:) (Clause ((:) (Atom "Vector.rect2.u1" 0)
    ([])) (Atom "Vector.nth_map2.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth.u0" 0) ([])) (Atom "Vector.nth_map2.u1" 0)) ((:) (Clause ((:)
    (Atom "Vector.map2.u1" 0) ([])) (Atom "Vector.nth_map2.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.nth_map2.u2" 0)) ((:)
    (Clause ((:) (Atom "Vector.nth.u0" 0) ([])) (Atom "Vector.nth_map2.u2"
    0)) ((:) (Clause ((:) (Atom "Vector.map2.u2" 0) ([])) (Atom
    "Vector.nth_map2.u2" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Vector.fold_left_right_assoc_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.fold_left.u1" 0) ([])) (Atom "Vector.fold_left_right_assoc_eq.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.fold_right.u1" 0) ([])) (Atom
    "Vector.fold_left_right_assoc_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.fold_left_right_assoc_eq.u1" 0))
    ((:) (Clause ((:) (Atom "Vector.fold_left.u0" 0) ([])) (Atom
    "Vector.fold_left_right_assoc_eq.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.fold_right.u0" 0) ([])) (Atom
    "Vector.fold_left_right_assoc_eq.u1" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Vector.take_O.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.take_O.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.take.u0" 0) ([])) (Atom "Vector.take_O.u0" 0)) ((:) (Clause
    ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.take_idem.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.take_idem.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.take_idem.u0" 0)) ((:) (Clause ((:) (Atom "Vector.take.u0" 0)
    ([])) (Atom "Vector.take_idem.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Vector.take_app.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.take_app.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.take_app.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.take.u0" 0) ([])) (Atom "Vector.take_app.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.append.u0" 0) ([])) (Atom
    "Vector.take_app.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.take_prf_irr.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10"
    0) ([])) (Atom "Vector.take_prf_irr.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.take_prf_irr.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.take.u0" 0) ([])) (Atom "Vector.take_prf_irr.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.uncons_cons.u0"
    0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([])) (Atom
    "Vector.uncons_cons.u0" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0) ([]))
    (Atom "Vector.uncons_cons.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0"
    0) ([])) (Atom "Vector.uncons_cons.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.uncons.u0" 0) ([])) (Atom "Vector.uncons_cons.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.append_comm_cons.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.append_comm_cons.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.append.u0" 0) ([])) (Atom "Vector.append_comm_cons.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.splitat_append.u0" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.splitat_append.u0" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([]))
    (Atom "Vector.splitat_append.u0" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0)
    ([])) (Atom "Vector.splitat_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.splitat_append.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.append.u0" 0) ([])) (Atom "Vector.splitat_append.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.splitat.u0" 0) ([])) (Atom
    "Vector.splitat_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.append_splitat.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom "prod.u0" 0) ([]))
    (Atom "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom "prod.u1" 0)
    ([])) (Atom "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom
    "pair_equal_spec.u0" 0) ([])) (Atom "Vector.append_splitat.u0" 0)) ((:)
    (Clause ((:) (Atom "pair_equal_spec.u1" 0) ([])) (Atom
    "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.hd.u0" 0) ([])) (Atom "Vector.append_splitat.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom "Vector.append_splitat.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.append.u0" 0) ([])) (Atom
    "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.splitat.u0" 0) ([])) (Atom "Vector.append_splitat.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.cons_inj.u0" 0) ([])) (Atom
    "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom "Vector.eta.u0" 0)
    ([])) (Atom "Vector.append_splitat.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.append_comm_cons.u0" 0) ([])) (Atom "Vector.append_splitat.u0"
    0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.Forall_impl.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10"
    0) ([])) (Atom "Vector.Forall_impl.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Vector.Forall_impl.u0" 0)) ((:) (Clause
    ((:) (Atom "sigT.u1" 0) ([])) (Atom "Vector.Forall_impl.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.Forall_impl.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.Forall.u0" 0) ([])) (Atom
    "Vector.Forall_impl.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom "Vector.Forall_impl.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.Forall_forall.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Vector.Forall_forall.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Vector.Forall_forall.u0" 0)) ((:) (Clause ((:) (Atom
    "sigT.u1" 0) ([])) (Atom "Vector.Forall_forall.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.Forall_forall.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.Forall.u0" 0) ([])) (Atom
    "Vector.Forall_forall.u0" 0)) ((:) (Clause ((:) (Atom "Vector.In.u0" 0)
    ([])) (Atom "Vector.Forall_forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom "Vector.Forall_forall.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.Forall_nth_order.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0)
    ([])) (Atom "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.Forall_nth_order.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.case0.u0" 0) ([])) (Atom
    "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom "Vector.hd.u0"
    0) ([])) (Atom "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order.u0" 0) ([])) (Atom "Vector.Forall_nth_order.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom
    "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.Forall.u0" 0) ([])) (Atom "Vector.Forall_nth_order.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom
    "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom "Vector.eta.u0"
    0) ([])) (Atom "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order_hd.u0" 0) ([])) (Atom "Vector.Forall_nth_order.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.nth_order_tl.u0" 0) ([])) (Atom
    "Vector.Forall_nth_order.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.Forall2_nth_order.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom "sigT.u1" 0)
    ([])) (Atom "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.Forall2_nth_order.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.case0.u0" 0) ([])) (Atom
    "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom "Vector.hd.u0"
    0) ([])) (Atom "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order.u0" 0) ([])) (Atom "Vector.Forall2_nth_order.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom
    "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.Forall2.u0" 0) ([])) (Atom "Vector.Forall2_nth_order.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.Forall2.u1" 0) ([])) (Atom
    "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom "Vector.Forall2_nth_order.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.eta.u0" 0) ([])) (Atom
    "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order_hd.u0" 0) ([])) (Atom "Vector.Forall2_nth_order.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.nth_order_tl.u0" 0) ([])) (Atom
    "Vector.Forall2_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.to_list_of_list_opp.u0" 0))
    ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Vector.to_list_of_list_opp.u0" 0)) ((:) (Clause ((:) (Atom "length.u0"
    0) ([])) (Atom "Vector.to_list_of_list_opp.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_of_list_opp.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.of_list.u0" 0) ([])) (Atom
    "Vector.to_list_of_list_opp.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_of_list_opp.u0" 0))
    ((:) (Clause ((:) (Atom "length.u0" 0) ([])) (Atom
    "Vector.length_to_list.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.length_to_list.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.length_to_list.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Init.Logic.9" 0) ([])) (Atom
    "Vector.of_list_to_list_opp.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.of_list_to_list_opp.u0" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.of_list_to_list_opp.u0" 0)) ((:) (Clause ((:) (Atom
    "map_subst_map.u1" 0) ([])) (Atom "Vector.of_list_to_list_opp.u0" 0))
    ((:) (Clause ((:) (Atom "map_subst_map.u3" 0) ([])) (Atom
    "Vector.of_list_to_list_opp.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Vector.of_list_to_list_opp.u0" 0)) ((:) (Clause ((:) (Atom
    "length.u0" 0) ([])) (Atom "Vector.of_list_to_list_opp.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.of_list_to_list_opp.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.case0.u0" 0) ([])) (Atom "Vector.of_list_to_list_opp.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.of_list.u0" 0) ([])) (Atom
    "Vector.of_list_to_list_opp.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.of_list_to_list_opp.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.length_to_list.u0" 0) ([])) (Atom
    "Vector.of_list_to_list_opp.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Vector.to_list_nil.u0" 0)) ((:) (Clause ((:) (Atom "list.u0"
    0) ([])) (Atom "Vector.to_list_nil.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_nil.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_nil.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.to_list_cons.u0"
    0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.to_list_cons.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Vector.to_list_cons.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0"
    0) ([])) (Atom "Vector.to_list_cons.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_cons.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom
    "Vector.to_list_hd.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.to_list_hd.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Vector.to_list_hd.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.to_list_hd.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.hd.u0" 0) ([])) (Atom "Vector.to_list_hd.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_hd.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.eta.u0" 0) ([])) (Atom
    "Vector.to_list_hd.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.44" 0)
    ([])) (Atom "Vector.to_list_last.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Vector.to_list_last.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Vector.to_list_last.u0" 0)) ((:) (Clause
    ((:) (Atom "list.u0" 0) ([])) (Atom "Vector.to_list_last.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_last.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.rectS.u0" 0) ([])) (Atom
    "Vector.to_list_last.u0" 0)) ((:) (Clause ((:) (Atom "Vector.last.u0" 0)
    ([])) (Atom "Vector.to_list_last.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_last.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.eta.u0" 0) ([])) (Atom
    "Vector.to_list_last.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list_cons.u0" 0) ([])) (Atom "Vector.to_list_last.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.857" 0) ([])) (Atom
    "Vector.to_list_const.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Vector.to_list_const.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Vector.to_list_const.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_const.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.const.u0" 0) ([])) (Atom "Vector.to_list_const.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_const.u0" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.44"
    0) ([])) (Atom "Vector.to_list_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Vector.to_list_nth_order.u0" 0)) ((:) (Clause
    ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom "Vector.to_list_nth_order.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.to_list_nth_order.u0" 0)) ((:) (Clause ((:) (Atom "Vector.hd.u0"
    0) ([])) (Atom "Vector.to_list_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order.u0" 0) ([])) (Atom "Vector.to_list_nth_order.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.tl.u0" 0) ([])) (Atom
    "Vector.to_list_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_nth_order.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.eta.u0" 0) ([])) (Atom
    "Vector.to_list_nth_order.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.nth_order_tl.u0" 0) ([])) (Atom "Vector.to_list_nth_order.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom
    "Vector.to_list_tl.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.to_list_tl.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Vector.to_list_tl.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Vector.to_list_tl.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_tl.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.tl.u0" 0) ([])) (Atom "Vector.to_list_tl.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_tl.u0" 0)) ((:) (Clause ((:) (Atom "Vector.eta.u0" 0)
    ([])) (Atom "Vector.to_list_tl.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.to_list_append.u0" 0)) ((:)
    (Clause ((:) (Atom "list.u0" 0) ([])) (Atom "Vector.to_list_append.u0"
    0)) ((:) (Clause ((:) (Atom "app.u0" 0) ([])) (Atom
    "Vector.to_list_append.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.to_list_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.append.u0" 0) ([])) (Atom "Vector.to_list_append.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list_cons.u0" 0) ([])) (Atom "Vector.to_list_append.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Vector.to_list_rev_append_tail.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0"
    0) ([])) (Atom "Vector.to_list_rev_append_tail.u0" 0)) ((:) (Clause ((:)
    (Atom "eq_ind_r.u0" 0) ([])) (Atom "Vector.to_list_rev_append_tail.u0"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "Vector.to_list_rev_append_tail.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_rev_append_tail.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.rev_append_tail.u0" 0) ([])) (Atom
    "Vector.to_list_rev_append_tail.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_rev_append_tail.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.247" 0) ([])) (Atom
    "Vector.to_list_rev_append.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0)
    ([])) (Atom "Vector.to_list_rev_append.u0" 0)) ((:) (Clause ((:) (Atom
    "eq_ind_r.u0" 0) ([])) (Atom "Vector.to_list_rev_append.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_rect_r.u1" 0) ([])) (Atom
    "Vector.to_list_rev_append.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Vector.to_list_rev_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_rev_append.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.rev_append_tail.u0" 0) ([])) (Atom
    "Vector.to_list_rev_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.rev_append.u0" 0) ([])) (Atom "Vector.to_list_rev_append.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_rev_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list_rev_append_tail.u0" 0) ([])) (Atom
    "Vector.to_list_rev_append.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.247" 0) ([])) (Atom "Vector.to_list_rev.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.to_list_rev.u0" 0))
    ((:) (Clause ((:) (Atom "eq_rect_r.u1" 0) ([])) (Atom
    "Vector.to_list_rev.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Vector.to_list_rev.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0"
    0) ([])) (Atom "Vector.to_list_rev.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.rev_append.u0" 0) ([])) (Atom "Vector.to_list_rev.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.rev.u0" 0) ([])) (Atom "Vector.to_list_rev.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_rev.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list_rev_append.u0" 0) ([])) (Atom "Vector.to_list_rev.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.277" 0) ([])) (Atom
    "Vector.to_list_map.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Vector.to_list_map.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0"
    0) ([])) (Atom "Vector.to_list_map.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.map.u0" 0) ([])) (Atom "Vector.to_list_map.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_map.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.278" 0) ([])) (Atom
    "Vector.to_list_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10"
    0) ([])) (Atom "Vector.to_list_map.u1" 0)) ((:) (Clause ((:) (Atom
    "list.u0" 0) ([])) (Atom "Vector.to_list_map.u1" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_map.u1" 0)) ((:)
    (Clause ((:) (Atom "Vector.map.u1" 0) ([])) (Atom "Vector.to_list_map.u1"
    0)) ((:) (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_map.u1" 0)) ((:) (Clause ((:) (Atom "Coq.Lists.List.377"
    0) ([])) (Atom "Vector.to_list_fold_left.u0" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "Vector.to_list_fold_left.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.fold_left.u1" 0) ([])) (Atom
    "Vector.to_list_fold_left.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.378" 0) ([])) (Atom "Vector.to_list_fold_left.u1" 0))
    ((:) (Clause ((:) (Atom "Vector.t.u0" 0) ([])) (Atom
    "Vector.to_list_fold_left.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.fold_left.u0" 0) ([])) (Atom "Vector.to_list_fold_left.u1" 0))
    ((:) (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_fold_left.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.381" 0) ([])) (Atom "Vector.to_list_fold_right.u0" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.to_list_fold_right.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.to_list_fold_right.u0" 0))
    ((:) (Clause ((:) (Atom "Vector.fold_right.u1" 0) ([])) (Atom
    "Vector.to_list_fold_right.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.382" 0) ([])) (Atom "Vector.to_list_fold_right.u1" 0))
    ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.to_list_fold_right.u1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Vector.to_list_fold_right.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_fold_right.u1" 0)) ((:)
    (Clause ((:) (Atom "Vector.fold_right.u0" 0) ([])) (Atom
    "Vector.to_list_fold_right.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_fold_right.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.702" 0) ([])) (Atom
    "Vector.to_list_Forall.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Vector.to_list_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.to_list_Forall.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.to_list_Forall.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([]))
    (Atom "Vector.to_list_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_Forall.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.Forall.u0" 0) ([])) (Atom "Vector.to_list_Forall.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_Forall.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.702" 0) ([])) (Atom "Vector.to_list_Exists.u0" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.to_list_Exists.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Vector.to_list_Exists.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Vector.to_list_Exists.u0" 0)) ((:) (Clause ((:) (Atom
    "list.u0" 0) ([])) (Atom "Vector.to_list_Exists.u0" 0)) ((:) (Clause ((:)
    (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_Exists.u0" 0)) ((:)
    (Clause ((:) (Atom "Vector.Exists.u0" 0) ([])) (Atom
    "Vector.to_list_Exists.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_Exists.u0" 0)) ((:)
    (Clause ((:) (Atom "Coq.Lists.List.1" 0) ([])) (Atom
    "Vector.to_list_In.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom
    "Vector.to_list_In.u0" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([]))
    (Atom "Vector.to_list_In.u0" 0)) ((:) (Clause ((:) (Atom "Vector.t.u0" 0)
    ([])) (Atom "Vector.to_list_In.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.In.u0" 0) ([])) (Atom "Vector.to_list_In.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_In.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.821" 0) ([])) (Atom
    "Vector.to_list_Forall2.u0" 0)) ((:) (Clause ((:) (Atom "eq.u0" 0) ([]))
    (Atom "Vector.to_list_Forall2.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Init.Logic.10" 0) ([])) (Atom "Vector.to_list_Forall2.u0" 0)) ((:)
    (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Vector.to_list_Forall2.u0" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Vector.to_list_Forall2.u0" 0)) ((:) (Clause ((:) (Atom
    "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_Forall2.u0" 0)) ((:) (Clause
    ((:) (Atom "Vector.Forall2.u0" 0) ([])) (Atom "Vector.to_list_Forall2.u0"
    0)) ((:) (Clause ((:) (Atom "Vector.to_list.u0" 0) ([])) (Atom
    "Vector.to_list_Forall2.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.821" 0) ([])) (Atom "Vector.to_list_Forall2.u1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Vector.to_list_Forall2.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Vector.to_list_Forall2.u1" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0)
    ([])) (Atom "Vector.to_list_Forall2.u1" 0)) ((:) (Clause ((:) (Atom
    "list.u0" 0) ([])) (Atom "Vector.to_list_Forall2.u1" 0)) ((:) (Clause
    ((:) (Atom "Vector.t.u0" 0) ([])) (Atom "Vector.to_list_Forall2.u1" 0))
    ((:) (Clause ((:) (Atom "Vector.case0.u0" 0) ([])) (Atom
    "Vector.to_list_Forall2.u1" 0)) ((:) (Clause ((:) (Atom "Vector.hd.u0" 0)
    ([])) (Atom "Vector.to_list_Forall2.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.tl.u0" 0) ([])) (Atom "Vector.to_list_Forall2.u1" 0)) ((:)
    (Clause ((:) (Atom "Vector.Forall2.u1" 0) ([])) (Atom
    "Vector.to_list_Forall2.u1" 0)) ((:) (Clause ((:) (Atom
    "Vector.to_list.u0" 0) ([])) (Atom "Vector.to_list_Forall2.u1" 0)) ((:)
    (Clause ((:) (Atom "Vector.eta.u0" 0) ([])) (Atom
    "Vector.to_list_Forall2.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.381" 0) ([])) (Atom "ZMicromega.cnf_of_list.u0" 0)) ((:)
    (Clause ((:) (Atom "prod.u1" 0) ([])) (Atom "ZMicromega.cnf_of_list.u0"
    0)) ((:) (Clause ((:) (Atom "list.u0" 0) ([])) (Atom
    "ZMicromega.cnf_of_list.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "ZMicromega.cnf_of_list.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.Lists.List.381" 0) ([])) (Atom
    "ZMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom "prod.u1"
    0) ([])) (Atom "ZMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:)
    (Atom "list.u0" 0) ([])) (Atom "ZMicromega.cnf_of_list_correct.u0" 0))
    ((:) (Clause ((:) (Atom "Refl.make_conj.u0" 0) ([])) (Atom
    "ZMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom
    "ZMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "ZMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "ZMicromega.cnf_of_list_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "ZMicromega.normalise.u0" 0))
    ((:) (Clause ((:) (Atom "ZMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "ZMicromega.normalise.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "ZMicromega.normalise_correct.u0"
    0)) ((:) (Clause ((:) (Atom "ZMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "ZMicromega.normalise_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "ZMicromega.cnf_of_list_correct.u0" 0) ([])) (Atom
    "ZMicromega.normalise_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "ZMicromega.normalise.u0" 0) ([])) (Atom
    "ZMicromega.normalise_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "ZMicromega.negate.u0" 0)) ((:)
    (Clause ((:) (Atom "ZMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "ZMicromega.negate.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.Tauto.52" 0) ([])) (Atom "ZMicromega.negate_correct.u0"
    0)) ((:) (Clause ((:) (Atom "ZMicromega.cnf_of_list.u0" 0) ([])) (Atom
    "ZMicromega.negate_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "ZMicromega.cnf_of_list_correct.u0" 0) ([])) (Atom
    "ZMicromega.negate_correct.u0" 0)) ((:) (Clause ((:) (Atom
    "ZMicromega.negate.u0" 0) ([])) (Atom "ZMicromega.negate_correct.u0" 0))
    ((:) (Clause ((:) (Atom "Coq.micromega.Tauto.52" 0) ([])) (Atom
    "ZMicromega.cnfZ.u0" 0)) ((:) (Clause ((:) (Atom
    "ZMicromega.normalise.u0" 0) ([])) (Atom "ZMicromega.cnfZ.u0" 0)) ((:)
    (Clause ((:) (Atom "ZMicromega.negate.u0" 0) ([])) (Atom
    "ZMicromega.cnfZ.u0" 0)) ((:) (Clause ((:) (Atom "Tauto.TFormula.u0" 0)
    ([])) (Atom "ZMicromega.cnfZ.u1" 0)) ((:) (Clause ((:) (Atom
    "Tauto.rxcnf.u0" 0) ([])) (Atom "ZMicromega.cnfZ.u1" 0)) ((:) (Clause
    ((:) (Atom "Tauto.TFormula.u1" 0) ([])) (Atom "ZMicromega.cnfZ.u2" 0))
    ((:) (Clause ((:) (Atom "Tauto.rxcnf.u1" 0) ([])) (Atom
    "ZMicromega.cnfZ.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Relations.Operators_Properties.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.1" 0) ([])) (Atom
    "Coq.Relations.Operators_Properties.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.2" 0) ([])) (Atom
    "Coq.Relations.Operators_Properties.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.3" 0) ([])) (Atom
    "Coq.Relations.Operators_Properties.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.4" 0) ([])) (Atom
    "Coq.Relations.Operators_Properties.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Operators.5" 0) ([])) (Atom
    "Coq.Relations.Operators_Properties.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Lists.List.1" 0) ([])) (Atom "Coq.setoid_ring.BinList.1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.setoid_ring.BinList.1" 0))
    ((:) (Clause ((:) (Atom "eq_ind_r.u0" 0) ([])) (Atom
    "Coq.setoid_ring.BinList.1" 0)) ((:) (Clause ((:) (Atom "list.u0" 0)
    ([])) (Atom "Coq.setoid_ring.BinList.1" 0)) ((:) (Clause ((:) (Atom
    "eq.u0" 0) ([])) (Atom "ssrclasses.eq_Reflexive.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.ssr.ssrclasses.1" 0) ([])) (Atom "ssrclasses.eq_Reflexive.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0)
    ([])) (Atom "Equivalence.equiv.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pequiv.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.equiv_reflexive_obligation_1.u0" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.equiv.u0" 0) ([])) (Atom
    "Equivalence.equiv_reflexive_obligation_1.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.equiv_symmetric_obligation_1.u0" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.equiv.u0" 0) ([])) (Atom
    "Equivalence.equiv_symmetric_obligation_1.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.equiv_transitive_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Equivalence.equiv.u0" 0) ([])) (Atom
    "Equivalence.equiv_transitive_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.respecting.u0" 0)) ((:) (Clause ((:) (Atom "sig.u0" 0) ([]))
    (Atom "Equivalence.respecting.u0" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.respecting.u2" 0) ([])) (Atom "Equivalence.respecting.u0"
    0)) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0)
    ([])) (Atom "Equivalence.respecting.u1" 0)) ((:) (Clause ((:) (Atom
    "sig.u0" 0) ([])) (Atom "Equivalence.respecting.u1" 0)) ((:) (Clause ((:)
    (Atom "Equivalence.respecting.u2" 0) ([])) (Atom
    "Equivalence.respecting.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.respecting.u2" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "sig.u0" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Equivalence.respecting.u0" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u0" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u1" 0)) ((:) (Clause ((:)
    (Atom "sig.u0" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Init.Specif.16" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u1" 0)) ((:) (Clause ((:)
    (Atom "Equivalence.respecting.u1" 0) ([])) (Atom
    "Equivalence.respecting_equiv_obligation_1.u1" 0)) ((:) (Clause ((:)
    (Atom "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_reflexive.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_reflexive.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_symmetric.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_symmetric.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_transitive.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_transitive.u1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u0" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_reflexive.u0" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u0" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_symmetric.u0" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u0" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_transitive.u0" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u1" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_reflexive.u1" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u1" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_symmetric.u1" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u1" 0)) ((:) (Clause ((:) (Atom
    "Equivalence.pointwise_transitive.u1" 0) ([])) (Atom
    "Equivalence.pointwise_equivalence.u1" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.default_relation.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "SetoidTactics.equivalence_default.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "GenericMinMax.gmax.u0" 0) ([])) (Atom "Coq.Structures.Equalities.1" 0))
    ((:) (Clause ((:) (Atom "GenericMinMax.gmin.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.ex_iff_morphism_obligation_1.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.all_iff_morphism_obligation_1.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.Acc_pt_morphism.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms_Prop.well_founded_morphism.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom "Coq.Init.Wf.1"
    0) ([])) (Atom "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "ex.u0" 0) ([])) (Atom "Coq.Structures.Equalities.1" 0)) ((:) (Clause
    ((:) (Atom "all.u0" 0) ([])) (Atom "Coq.Structures.Equalities.1" 0)) ((:)
    (Clause ((:) (Atom "eq.u0" 0) ([])) (Atom "Coq.Structures.Equalities.1"
    0)) ((:) (Clause ((:) (Atom "Coq.Init.Logic.10" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom "eq_ind_r.u0"
    0) ([])) (Atom "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Basics.flip.u0" 0) ([])) (Atom "Coq.Structures.Equalities.1" 0)) ((:)
    (Clause ((:) (Atom "Basics.flip.u1" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom "CompSpec.u0"
    0) ([])) (Atom "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "CompSpec2Type.u0" 0) ([])) (Atom "Coq.Structures.Equalities.1" 0)) ((:)
    (Clause ((:) (Atom "Coq.Classes.Morphisms.31" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff.u0" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff_2.u1" 0) ([])) (Atom
    "Coq.Structures.Equalities.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Classes.RelationClasses.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.RelationClasses.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "RelationClasses.Tlist.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.Tlist.u0" 0) ([])) (Atom
    "RelationClasses.binary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "RelationClasses.arrows.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.arrows.u0" 0) ([])) (Atom
    "RelationClasses.binary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "RelationClasses.arrows.u1" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.arrows.u1" 0) ([])) (Atom
    "RelationClasses.binary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "RelationClasses.binary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_operation.u0" 0) ([])) (Atom
    "RelationClasses.binary_relation.u0" 0)) ((:) (Clause ((:) (Atom
    "RelationClasses.binary_relation.u0" 0) ([])) (Atom
    "RelationClasses.binary_operation.u0" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Classes.RelationClasses.67" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.RelationClasses.67" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.micromega.EnvRing.10" 0) ([])) (Atom "Coq.micromega.RingMicromega.2"
    0)) ((:) (Clause ((:) (Atom "Coq.micromega.RingMicromega.2" 0) ([]))
    (Atom "Coq.micromega.EnvRing.10" 0)) ((:) (Clause ((:) (Atom
    "induction_ltof1.u0" 0) ([])) (Atom "induction_gtof1.u0" 0)) ((:) (Clause
    ((:) (Atom "induction_gtof1.u0" 0) ([])) (Atom "induction_ltof1.u0" 0))
    ((:) (Clause ((:) (Atom "well_founded_induction_type.u0" 0) ([])) (Atom
    "induction_ltof2.u0" 0)) ((:) (Clause ((:) (Atom "induction_ltof2.u0" 0)
    ([])) (Atom "well_founded_induction_type.u0" 0)) ((:) (Clause ((:) (Atom
    "well_founded_induction_type.u0" 0) ([])) (Atom "induction_gtof2.u0" 0))
    ((:) (Clause ((:) (Atom "induction_gtof2.u0" 0) ([])) (Atom
    "well_founded_induction_type.u0" 0)) ((:) (Clause ((:) (Atom
    "lt_wf_rect.u0" 0) ([])) (Atom "gt_wf_rect.u0" 0)) ((:) (Clause ((:)
    (Atom "gt_wf_rect.u0" 0) ([])) (Atom "lt_wf_rect.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Logic.EqdepFacts.82" 0) ([])) (Atom
    "BinPos.Pos.eq_dep_eq_positive.u0" 0)) ((:) (Clause ((:) (Atom
    "BinPos.Pos.eq_dep_eq_positive.u0" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.82" 0)) ((:) (Clause ((:) (Atom "Vector.cast.u0" 0)
    ([])) (Atom "Vector.cast.u1" 0)) ((:) (Clause ((:) (Atom "Vector.cast.u1"
    0) ([])) (Atom "Vector.cast.u0" 0)) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom
    "ssrunder.Under_rel.Over_rel.u0" 0)) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Over_rel.u0" 0) ([])) (Atom
    "ssrunder.Under_rel.Under_rel.u0" 0)) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_rel.u0" 0) ([])) (Atom "Coq.ssr.ssrunder.8" 0))
    ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.8" 0) ([])) (Atom
    "ssrunder.Under_rel.Under_rel.u0" 0)) ((:) (Clause ((:) (Atom
    "ssrunder.Under_rel.Under_rel_from_rel.u0" 0) ([])) (Atom
    "Coq.ssr.ssrunder.9" 0)) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.9" 0)
    ([])) (Atom "ssrunder.Under_rel.Under_rel_from_rel.u0" 0)) ((:) (Clause
    ((:) (Atom "ssrunder.Under_rel.Under_relE.u0" 0) ([])) (Atom
    "Coq.ssr.ssrunder.10" 0)) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.10"
    0) ([])) (Atom "ssrunder.Under_rel.Under_relE.u0" 0)) ((:) (Clause ((:)
    (Atom "ssrunder.Under_rel.over_rel.u0" 0) ([])) (Atom
    "Coq.ssr.ssrunder.11" 0)) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.11"
    0) ([])) (Atom "ssrunder.Under_rel.over_rel.u0" 0)) ((:) (Clause ((:)
    (Atom "ssrunder.Under_rel.over_rel_done.u0" 0) ([])) (Atom
    "Coq.ssr.ssrunder.12" 0)) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.12"
    0) ([])) (Atom "ssrunder.Under_rel.over_rel_done.u0" 0)) ((:) (Clause
    ((:) (Atom "ssrunder.Under_rel.under_rel_done.u0" 0) ([])) (Atom
    "Coq.ssr.ssrunder.13" 0)) ((:) (Clause ((:) (Atom "Coq.ssr.ssrunder.13"
    0) ([])) (Atom "ssrunder.Under_rel.under_rel_done.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Logic.EqdepFacts.82" 0) ([])) (Atom
    "Eqdep_dec.eq_dep_eq_dec.u1" 0)) ((:) (Clause ((:) (Atom
    "Eqdep_dec.eq_dep_eq_dec.u1" 0) ([])) (Atom "Coq.Logic.EqdepFacts.82" 0))
    ((:) (Clause ((:) (Atom "Eqdep_dec.eq_rect_eq_dec.u1" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.15" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.15" 0) ([])) (Atom "Eqdep_dec.eq_rect_eq_dec.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.82" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.16" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.16" 0) ([])) (Atom "Coq.Logic.EqdepFacts.82" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.17" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.17" 0) ([])) (Atom "Coq.Logic.EqdepFacts.84" 0))
    ((:) (Clause ((:) (Atom "Eqdep_dec.eq_rect_eq_dec.u1" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.18" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.18" 0) ([])) (Atom "Eqdep_dec.eq_rect_eq_dec.u1" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.82" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.19" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.19" 0) ([])) (Atom "Coq.Logic.EqdepFacts.82" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom
    "Coq.Logic.Eqdep_dec.20" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.Eqdep_dec.20" 0) ([])) (Atom "Coq.Logic.EqdepFacts.84" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom
    "Eqdep_dec.inj_pair2_eq_dec.u1" 0)) ((:) (Clause ((:) (Atom
    "Eqdep_dec.inj_pair2_eq_dec.u1" 0) ([])) (Atom "Coq.Logic.EqdepFacts.84"
    0)) ((:) (Clause ((:) (Atom "Coq.Relations.Relation_Definitions.1" 0)
    ([])) (Atom "Coq.Classes.Morphisms.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.1" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Coq.Classes.Morphisms.11" 0)) ((:) (Clause ((:) (Atom
    "Coq.Classes.Morphisms.11" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Coq.Relations.Relation_Definitions.1" 0) ([])) (Atom
    "Morphisms.proper_sym_impl_iff_2.u0" 0)) ((:) (Clause ((:) (Atom
    "Morphisms.proper_sym_impl_iff_2.u0" 0) ([])) (Atom
    "Coq.Relations.Relation_Definitions.1" 0)) ((:) (Clause ((:) (Atom
    "Tauto.rtyp.u0" 0) ([])) (Atom "Tauto.eKind.u0" 0)) ((:) (Clause ((:)
    (Atom "Tauto.eKind.u0" 0) ([])) (Atom "Tauto.rtyp.u0" 0)) ((:) (Clause
    ((:) (Atom "Coq.Logic.EqdepFacts.81" 0) ([])) (Atom
    "EqdepFacts.Eq_rect_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_rect_eq.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.81" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.82" 0) ([])) (Atom
    "EqdepFacts.Eq_dep_eq.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Eq_dep_eq.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.82" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.84" 0) ([])) (Atom
    "EqdepFacts.Inj_dep_pair.u0" 0)) ((:) (Clause ((:) (Atom
    "EqdepFacts.Inj_dep_pair.u0" 0) ([])) (Atom "Coq.Logic.EqdepFacts.84" 0))
    ((:) (Clause ((:) (Atom "Coq.Logic.EqdepFacts.81" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.79" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.79" 0) ([])) (Atom "Coq.Logic.EqdepFacts.81" 0))
    ((:) (Clause ((:) (Atom "Eqdep_dec.eq_rect_eq_dec.u1" 0) ([])) (Atom
    "Coq.Logic.EqdepFacts.81" 0)) ((:) (Clause ((:) (Atom
    "Coq.Logic.EqdepFacts.81" 0) ([])) (Atom "Eqdep_dec.eq_rect_eq_dec.u1"
    0))
    ([]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

f4 :: Frontier
f4 =
  frontier_fin_0

vars'4 :: ([]) Prelude.String
vars'4 =
  nodup ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
    (vars cs4)

ex_coq_types :: Ex_lfp_geq -> Ex_lfp_geq
ex_coq_types x =
  thm_32 (length vars'4) (length vars'4) cs4 vars'4 ([]) f4 x

ex_lfp_geq_empty_coq_types :: Ex_lfp_geq
ex_lfp_geq_empty_coq_types =
  ex_lfp_geq_empty cs4 f4

main :: Prelude.IO ()
main =
    Prelude.print ((ex_coq_types ex_lfp_geq_empty_coq_types) "Prop")
