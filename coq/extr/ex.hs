module Ex where

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
eq_rect _ f4 _ =
  f4

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f4 f5 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f4)
    (\n0 -> f5 n0 (nat_rect f4 f5 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f4 f5 l =
  case l of {
   ([]) -> f4;
   (:) y l0 -> f5 y l0 (list_rect f4 f5 l0)}

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
sig_rect f4 s =
  f4 s __

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
flat_map f4 l =
  case l of {
   ([]) -> ([]);
   (:) x t -> app (f4 x) (flat_map f4 t)}

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
update_infty_V v f4 x =
  case set_mem
         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
         v of {
   Prelude.True -> Infty;
   Prelude.False -> f4 x}

data Atom0 =
   Atom Prelude.String Prelude.Integer

atom_true :: Atom0 -> Frontier -> Prelude.Bool
atom_true a f4 =
  case a of {
   Atom x k ->
    case f4 x of {
     Infty -> Prelude.True;
     Fin n -> (Prelude.<=) k n}}

shift_atom :: Prelude.Integer -> Atom0 -> Atom0
shift_atom n a =
  case a of {
   Atom x k -> Atom x ((Prelude.+) n k)}

data Clause0 =
   Clause (Set Atom0) Atom0

clause_true :: Clause0 -> Frontier -> Prelude.Bool
clause_true c f4 =
  case c of {
   Clause conds conc ->
    case fold_right (Prelude.&&) Prelude.True
           (map (\a -> atom_true a f4) conds) of {
     Prelude.True -> atom_true conc f4;
     Prelude.False -> Prelude.True}}

shift_clause :: Prelude.Integer -> Clause0 -> Clause0
shift_clause n c =
  case c of {
   Clause conds conc -> Clause (map (shift_atom n) conds) (shift_atom n conc)}

all_shifts_true :: Clause0 -> Frontier -> Prelude.Bool
all_shifts_true c f4 =
  case c of {
   Clause _ conc ->
    case conc of {
     Atom x k ->
      case f4 x of {
       Infty -> Prelude.True;
       Fin n ->
        clause_true (shift_clause (sub ((Prelude.+) n (Prelude.succ 0)) k) c)
          f4}}}

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
vars cs4 =
  flat_map vars_clause cs4

sub_vars_improvable :: (Set Clause0) -> (Set Prelude.String) -> (Set
                       Prelude.String) -> Frontier -> Set Prelude.String
sub_vars_improvable cs4 v w f4 =
  case cs4 of {
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
               (all_shifts_true (Clause l (Atom x k)) f4) of {
         Prelude.True -> sub_vars_improvable t v w f4;
         Prelude.False ->
          set_add
            ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x (sub_vars_improvable t v w f4)}}}}

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
ex_lfp_geq_empty _ f4 =
  f4

ex_lfp_geq_nodup_iff :: (Set Clause0) -> (Set Prelude.String) -> Frontier ->
                        (,) (Ex_lfp_geq -> Ex_lfp_geq)
                        (Ex_lfp_geq -> Ex_lfp_geq)
ex_lfp_geq_nodup_iff _ _ _ =
  (,) (\h -> sig_rec (\x _ -> x) h) (\h -> sig_rec (\x _ -> x) h)

sub_forward :: (Set Clause0) -> (Set Prelude.String) -> (Set Prelude.String)
               -> Frontier -> (,) (Set Prelude.String) Frontier
sub_forward cs4 v w f4 =
  let {x = sub_vars_improvable cs4 v w f4} in
  let {
   f' = \v0 ->
    case set_mem
           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           v0 x of {
     Prelude.True -> sinfty (f4 v0);
     Prelude.False -> f4 v0}}
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
thm_32 n m cs4 v w f4 x =
  nat_rect (\_ _ _ _ f5 _ _ _ _ -> f5) (\n0 iHn m0 ->
    Debug.Trace.trace
        ("IHn: n = " ++ Prelude.show n0 ++ ", m = " ++ Prelude.show m0 ++
        ", v = " ++ (Prelude.show v) ++ ", w = " ++ (Prelude.show w) ++
        Prelude.concatMap (\var -> ", f(" ++ var ++ ") = " ++ Prelude.show (f4 var)) v) Prelude.$
    nat_rect (\cs5 v0 w0 f5 _ _ _ h2 ->
      ex_lfp_geq_incl cs5
        (nodup
          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          v0)
        (nodup
          ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
          w0) f5 h2) (\m1 iHm cs5 v0 w0 f5 _ _ _ h2 ->
            Debug.Trace.trace
                ("IHm: n = " ++ Prelude.show (Prelude.succ n0) ++ ", m = " ++ Prelude.show m1 ++
                ", v = " ++ (Prelude.show v0) ++ ", w = " ++ (Prelude.show w0) ++
                Prelude.concatMap (\var -> ", f(" ++ var ++ ") = " ++ Prelude.show (f5 var)) v) Prelude.$
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
       Prelude.True -> iHm cs5 v0 w0 f5 __ __ __ h2;
       Prelude.False ->
        let {h5 = iHn n0 cs5 w0 ([]) f5 __ __ __ f5} in
        let {
         h = lem_33 cs5 v0
               (nodup
                 ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 w0) f5 (\cs' v' w' f' m2 _ _ _ h9 ->
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
           p = sub_forward cs5
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
              (sub_vars_improvable cs5
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
                       (sub_vars_improvable cs5
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
                    Prelude.True -> update_infty_V v0 f5;
                    Prelude.False ->
                     ex_lfp_geq_monotone cs5
                       (nodup
                         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                         v0) b f5
                       (iHm cs5 v0
                         (nodup
                           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           (set_union
                             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             w0 a)) b __ __ __
                         (iHn n0 cs5
                           (nodup
                             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             (set_union
                               ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                               w0 a)) ([]) b __ __ __ b))}}) b) a __}) h}) m0)
    n m cs4 v w f4 __ __ __ x

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

