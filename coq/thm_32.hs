module Thm_32 where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

nat_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
nat_rec =
  nat_rect

list_rect :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rect f f0 l =
  case l of {
   ([]) -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (([]) a1) -> a2 -> a2) -> (([]) a1) -> a2
list_rec =
  list_rect

length :: (([]) a1) -> Prelude.Integer
length l =
  case l of {
   ([]) -> 0;
   (:) _ l' -> Prelude.succ (length l')}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub = (\n m -> Prelude.max 0 (n Prelude.- m))

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

in_dec :: (a1 -> a1 -> Prelude.Bool) -> a1 -> (([]) a1) -> Prelude.Bool
in_dec h a l =
  list_rec Prelude.False (\a0 _ iHl ->
    let {s = h a0 a} in
    case s of {
     Prelude.True -> Prelude.True;
     Prelude.False -> iHl}) l

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map = Prelude.map

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

sinfty :: Ninfty -> Ninfty
sinfty x =
  case x of {
   Infty -> Infty;
   Fin n -> Fin (Prelude.succ n)}

type Frontier = Prelude.String -> Ninfty

frontier_fin_0 :: Frontier
frontier_fin_0 _ =
  Fin 0

update_infty_V :: (Set Prelude.String) -> Frontier -> Frontier
update_infty_V v f x =
  case set_mem
         ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool) x
         v of {
   Prelude.True -> Infty;
   Prelude.False -> f x}

data Atom0 =
   Atom Prelude.String Prelude.Integer

x_str :: Prelude.String
x_str =
  "x"

y_str :: Prelude.String
y_str =
  "y"

z_str :: Prelude.String
z_str =
  "z"

u_str :: Prelude.String
u_str =
  "u"

atom_x0 :: Atom0
atom_x0 =
  Atom "x" 0

atom_x1 :: Atom0
atom_x1 =
  Atom "x" (Prelude.succ 0)

atom_y0 :: Atom0
atom_y0 =
  Atom "y" 0

atom_y1 :: Atom0
atom_y1 =
  Atom "y" (Prelude.succ 0)

atom_z0 :: Atom0
atom_z0 =
  Atom "z" 0

atom_z1 :: Atom0
atom_z1 =
  Atom "z" (Prelude.succ 0)

atom_u0 :: Atom0
atom_u0 =
  Atom "u" 0

atom_u1 :: Atom0
atom_u1 =
  Atom "u" (Prelude.succ 0)

atom_true :: Atom0 -> Frontier -> Prelude.Bool
atom_true a f =
  case a of {
   Atom x k ->
    case f x of {
     Infty -> Prelude.True;
     Fin n -> (Prelude.<=) k n}}

shift_atom :: Prelude.Integer -> Atom0 -> Atom0
shift_atom n a =
  case a of {
   Atom x k -> Atom x ((Prelude.+) n k)}

data Clause0 =
   Clause (Set Atom0) Atom0

clause_true :: Clause0 -> Frontier -> Prelude.Bool
clause_true c f =
  case c of {
   Clause conds conc ->
    case fold_right (Prelude.&&) Prelude.True
           (map (\a -> atom_true a f) conds) of {
     Prelude.True -> atom_true conc f;
     Prelude.False -> Prelude.True}}

shift_clause :: Prelude.Integer -> Clause0 -> Clause0
shift_clause n c =
  case c of {
   Clause conds conc -> Clause (map (shift_atom n) conds) (shift_atom n conc)}

all_shifts_true :: Clause0 -> Frontier -> Prelude.Bool
all_shifts_true c f =
  case c of {
   Clause _ conc ->
    case conc of {
     Atom x k ->
      case f x of {
       Infty -> Prelude.True;
       Fin n ->
        clause_true (shift_clause (sub ((Prelude.+) n (Prelude.succ 0)) k) c)
          f}}}

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

sub_vars_improvable :: (Set Clause0) -> (Set Prelude.String) -> (Set
                       Prelude.String) -> Frontier -> Set Prelude.String
sub_vars_improvable cs v w f =
  case cs of {
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
               (all_shifts_true (Clause l (Atom x k)) f) of {
         Prelude.True -> sub_vars_improvable t v w f;
         Prelude.False ->
          set_add
            ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
            x (sub_vars_improvable t v w f)}}}}

type Ex_lfp_geq = Frontier

ex_lfp_geq_incl :: (Set Clause0) -> (Set Prelude.String) -> (Set
                   Prelude.String) -> Frontier -> Ex_lfp_geq -> Ex_lfp_geq
ex_lfp_geq_incl _ _ _ _ h0 =
  h0

ex_lfp_geq_monotone :: (Set Clause0) -> (Set Prelude.String) -> Frontier ->
                       Frontier -> Ex_lfp_geq -> Ex_lfp_geq
ex_lfp_geq_monotone _ _ _ _ h =
  h

ex_lfp_geq_empty :: (Set Clause0) -> Frontier -> Ex_lfp_geq
ex_lfp_geq_empty _ f =
  f

ex_lfp_geq_nodup_iff :: (Set Clause0) -> (Set Prelude.String) -> Frontier ->
                        (,) (Ex_lfp_geq -> Ex_lfp_geq)
                        (Ex_lfp_geq -> Ex_lfp_geq)
ex_lfp_geq_nodup_iff _ _ _ =
  (,) (\h -> sig_rec (\x _ -> x) h) (\h -> sig_rec (\x _ -> x) h)

sub_forward :: (Set Clause0) -> (Set Prelude.String) -> (Set Prelude.String)
               -> Frontier -> (,) (Set Prelude.String) Frontier
sub_forward cs v w f =
  let {x = sub_vars_improvable cs v w f} in
  let {
   f' = \v0 ->
    case set_mem
           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
           v0 x of {
     Prelude.True -> sinfty (f v0);
     Prelude.False -> f v0}}
  in
  (,) x f'

lem_33 :: (Set Clause0) -> (Set Prelude.String) -> (Set Prelude.String) ->
          Frontier -> Ex_lfp_geq -> Ex_lfp_geq
lem_33 =
  Prelude.error "AXIOM TO BE REALIZED"

thm_32 :: (Set Clause0) -> Prelude.Integer -> Prelude.Integer -> Frontier ->
          (Set Prelude.String) -> (Set Prelude.String) -> Ex_lfp_geq ->
          Ex_lfp_geq
thm_32 cs n m f v w x =
  nat_rect (\_ f0 _ _ _ _ _ _ -> f0) (\n0 iHn m0 ->
    nat_rect (\f0 v0 w0 _ _ _ h2 -> ex_lfp_geq_incl cs v0 w0 f0 h2)
      (\m1 iHm f0 v0 w0 _ _ _ h2 ->
      let {
       h3 = le_lt_eq_dec
              (length
                (set_diff
                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  v0 w0)) (Prelude.succ m1)}
      in
      case h3 of {
       Prelude.True -> iHm f0 v0 w0 __ __ __ h2;
       Prelude.False ->
        let {
         h5 = iHn n0 f0
                (nodup
                  ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                  w0) ([]) __ __ __ f0}
        in
        let {
         h = lem_33 cs v0
               (nodup
                 ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                 w0) f0 h5}
        in
        sig_rec (\h0 _ ->
          let {p = sub_forward cs v0 v0 h0} in
          case p of {
           (,) a b ->
            eq_rect (sub_vars_improvable cs v0 v0 h0) (\_ ->
              eq_rect (\v1 ->
                case set_mem
                       ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                       v1 (sub_vars_improvable cs v0 v0 h0) of {
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
                              w0 a))}
                   in
                   case s of {
                    Prelude.True -> update_infty_V v0 f0;
                    Prelude.False ->
                     ex_lfp_geq_monotone cs v0 b f0
                       (iHm b v0
                         (set_union
                           ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                           w0 a) __ __ __
                         (iHn n0 b
                           (set_union
                             ((Prelude.==) :: Prelude.String -> Prelude.String -> Prelude.Bool)
                             w0 a) ([]) __ __ __ b))}}) b) a __}) h}) m0) n m
    f v w __ __ __ x

cs_ex_1 :: ([]) Clause0
cs_ex_1 =
  (:) (Clause ((:) atom_x0 ([])) atom_x0) ([])

f_ex_1 :: Frontier
f_ex_1 =
  frontier_fin_0

thm_32_example1 :: Ex_lfp_geq -> Ex_lfp_geq
thm_32_example1 x =
  thm_32 cs_ex_1 (Prelude.succ 0) (Prelude.succ 0) f_ex_1 ((:) x_str ([]))
    ([]) x

ex_lfp_geq_empty_1 :: Ex_lfp_geq
ex_lfp_geq_empty_1 =
  ex_lfp_geq_empty cs_ex_1 f_ex_1

cs_ex_2 :: ([]) Clause0
cs_ex_2 =
  (:) (Clause ((:) atom_x0 ([])) atom_x1) ([])

f_ex_2 :: Frontier
f_ex_2 =
  frontier_fin_0

thm_32_example2 :: Ex_lfp_geq -> Ex_lfp_geq
thm_32_example2 x =
  thm_32 cs_ex_2 (Prelude.succ 0) (Prelude.succ 0) f_ex_2 ((:) x_str ([]))
    ([]) x

ex_lfp_geq_empty_2 :: Ex_lfp_geq
ex_lfp_geq_empty_2 =
  ex_lfp_geq_empty cs_ex_2 f_ex_2

cs_ex_3 :: ([]) Clause0
cs_ex_3 =
  (:) (Clause ((:) atom_x0 ([])) atom_y1) ([])

f_ex_3 :: Frontier
f_ex_3 =
  frontier_fin_0

thm_32_example3 :: Ex_lfp_geq -> Ex_lfp_geq
thm_32_example3 x =
  thm_32 cs_ex_3 (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ
    0)) f_ex_3 ((:) x_str ((:) y_str ([]))) ([]) x

ex_lfp_geq_empty_3 :: Ex_lfp_geq
ex_lfp_geq_empty_3 =
  ex_lfp_geq_empty cs_ex_3 f_ex_3

cs_ex_4 :: ([]) Clause0
cs_ex_4 =
  (:) (Clause ((:) atom_x0 ([])) atom_y1) ((:) (Clause ((:) atom_z0 ([]))
    atom_x1) ([]))

f_ex_4 :: Frontier
f_ex_4 =
  frontier_fin_0

thm_32_example4 :: Ex_lfp_geq -> Ex_lfp_geq
thm_32_example4 x =
  thm_32 cs_ex_4 (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ
    (Prelude.succ (Prelude.succ 0))) f_ex_4 ((:) x_str ((:) y_str ((:) z_str
    ([])))) ([]) x

ex_lfp_geq_empty_4 :: Ex_lfp_geq
ex_lfp_geq_empty_4 =
  ex_lfp_geq_empty cs_ex_4 f_ex_4

cs_ex_5 :: ([]) Clause0
cs_ex_5 =
  (:) (Clause ((:) atom_x0 ((:) atom_y0 ([]))) atom_x1) ((:) (Clause ((:)
    atom_x0 ((:) atom_y0 ([]))) atom_y1) ([]))

f_ex_5 :: Frontier
f_ex_5 =
  frontier_fin_0

thm_32_example5 :: Ex_lfp_geq -> Ex_lfp_geq
thm_32_example5 x =
  thm_32 cs_ex_5 (Prelude.succ (Prelude.succ 0)) (Prelude.succ (Prelude.succ
    0)) f_ex_5 ((:) x_str ((:) y_str ([]))) ([]) x

ex_lfp_geq_empty_5 :: Ex_lfp_geq
ex_lfp_geq_empty_5 =
  ex_lfp_geq_empty cs_ex_5 f_ex_5

cs_ex_6 :: ([]) Clause0
cs_ex_6 =
  (:) (Clause ((:) atom_x0 ([])) atom_y1) ((:) (Clause ((:) atom_y0 ((:)
    atom_z0 ([]))) atom_z1) ([]))

f_ex_6 :: Frontier
f_ex_6 =
  frontier_fin_0

thm_32_example6 :: Ex_lfp_geq -> Ex_lfp_geq
thm_32_example6 x =
  thm_32 cs_ex_6 (Prelude.succ (Prelude.succ (Prelude.succ 0))) (Prelude.succ
    (Prelude.succ (Prelude.succ 0))) f_ex_6 ((:) x_str ((:) y_str ((:) z_str
    ([])))) ([]) x

ex_lfp_geq_empty_6 :: Ex_lfp_geq
ex_lfp_geq_empty_6 =
  ex_lfp_geq_empty cs_ex_6 f_ex_6

cs_ex_7 :: ([]) Clause0
cs_ex_7 =
  (:) (Clause ((:) atom_x0 ([])) atom_x1) ((:) (Clause ((:) atom_y0 ([]))
    atom_z1) ((:) (Clause ((:) atom_z0 ([])) atom_u1) ([])))

f_ex_7 :: Frontier
f_ex_7 =
  frontier_fin_0

thm_32_example7 :: Ex_lfp_geq -> Ex_lfp_geq
thm_32_example7 x =
  thm_32 cs_ex_7 (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ
    0)))) (Prelude.succ (Prelude.succ (Prelude.succ (Prelude.succ 0))))
    f_ex_7 ((:) x_str ((:) y_str ((:) z_str ((:) u_str ([]))))) ([]) x

ex_lfp_geq_empty_7 :: Ex_lfp_geq
ex_lfp_geq_empty_7 =
  ex_lfp_geq_empty cs_ex_7 f_ex_7

