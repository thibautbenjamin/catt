  $ catt --no-builtins features/vanilla.catt
  [=^.^=] coh id = x -> x
  [=I.I=] successfully defined id.
  [=^.^=] coh comp = x -> z
  [=I.I=] successfully defined comp.
  [=^.^=] coh whiskr = (comp  x y f z g) -> (comp  x y f' z g)
  [=I.I=] successfully defined whiskr.
  [=^.^=] coh whiskl = (comp  x y f z g) -> (comp  x y f z g')
  [=I.I=] successfully defined whiskl.
  [=^.^=] coh horiz = (comp  x y f z g) -> (comp  x y f' z g')
  [=I.I=] successfully defined horiz.
  [=^.^=] let sq = (comp  x x f x f)
  [=I.I=] successfully defined term (comp f f) of type x -> x.
  [=^.^=] let cbd = (comp  x x f x (comp  x x f x f))
  [=I.I=] successfully defined term (comp f (comp f f)) of type x -> x.
  [=^.^=] coh simpl = (sq  x (id  x)) -> (id  x)
  [=I.I=] successfully defined simpl.
  [=^.^=] check (comp  x x (sq  x f) x (cbd  x f))
  [=I.I=] valid term (comp (sq f) (cbd f)) of type x -> x.

  $ catt --no-builtins features/unification.catt
  [=^.^=] coh id = x -> x
  [=I.I=] successfully defined id.
  [=^.^=] coh comp = x -> z
  [=I.I=] successfully defined comp.
  [=^.^=] coh whiskr = (comp  f g) -> (comp  f' g)
  [=I.I=] successfully defined whiskr.
  [=^.^=] coh whiskl = (comp  f g) -> (comp  f g')
  [=I.I=] successfully defined whiskl.
  [=^.^=] coh horiz = (comp  f g) -> (comp  f' g')
  [=I.I=] successfully defined horiz.
  [=^.^=] let sq = (comp  f f)
  [=I.I=] successfully defined term (comp f f) of type x -> x.
  [=^.^=] let cbd = (comp  f (comp  f f))
  [=I.I=] successfully defined term (comp f (comp f f)) of type x -> x.
  [=^.^=] coh simpl = (sq  (id  x)) -> (id  x)
  [=I.I=] successfully defined simpl.
  [=^.^=] check (comp  (sq  f) (cbd  f))
  [=I.I=] valid term (comp (sq f) (cbd f)) of type x -> x.

  $ catt --no-builtins features/wildcards.catt
  [=^.^=] coh id = x -> x
  [=I.I=] successfully defined id.
  [=^.^=] coh comp = x -> z
  [=I.I=] successfully defined comp.
  [=^.^=] coh unitr = (comp  f (id  _)) -> f
  [=I.I=] successfully defined unitr.
  [=^.^=] coh unitl = (comp  (id  _) f) -> f
  [=I.I=] successfully defined unitl.

  $ catt --no-builtins features/ps-syntax.catt
  [=^.^=] coh id = x -> x
  [=I.I=] successfully defined id.
  [=^.^=] coh comp = x -> z
  [=I.I=] successfully defined comp.
  [=^.^=] coh whiskr = (comp  f g) -> (comp  f' g)
  [=I.I=] successfully defined whiskr.
  [=^.^=] coh whiskl = (comp  f g) -> (comp  f g')
  [=I.I=] successfully defined whiskl.
  [=^.^=] coh horiz = (comp  f g) -> (comp  f' g')
  [=I.I=] successfully defined horiz.
  [=^.^=] let sq = (comp  f f)
  [=I.I=] successfully defined term (comp f f) of type x -> x.
  [=^.^=] let cbd = (comp  f (comp  f f))
  [=I.I=] successfully defined term (comp f (comp f f)) of type x -> x.
  [=^.^=] coh simpl = (sq  (id  x)) -> (id  x)
  [=I.I=] successfully defined simpl.
  [=^.^=] check (comp  (sq  f) (cbd  f))
  [=I.I=] valid term (comp (sq f) (cbd f)) of type x -> x.
  [=^.^=] let comp-bis = (comp  f g)
  [=I.I=] successfully defined term (comp f g) of type x -> z.

  $ catt features/builtins.catt
  [=^.^=] coh unit = (_builtin_comp  f (_builtin_id  _)) -> f
  [=I.I=] successfully defined unit.
  [=^.^=] coh unbiase = (_builtin_comp  (_builtin_comp  f g) h) -> (_builtin_comp  f g h)
  [=I.I=] successfully defined unbiase.
  [=^.^=] coh unit_bis = (_builtin_comp  x y f y (_builtin_id  y)) -> f
  [=I.I=] successfully defined unit.
  [=^.^=] coh unbiase = (_builtin_comp  _ _ (_builtin_comp  _ _ f _ g) _ h) -> (_builtin_comp  _ _ f _ g _ h)
  [=I.I=] successfully defined unbiase.

  $ catt features/contexts.catt
  [=^.^=] coh whisk = (_builtin_comp  f h) -> (_builtin_comp  g h)
  [=I.I=] successfully defined whisk.
  [=^.^=] let composition = (whisk  a h)
  [=I.I=] successfully defined term (whisk a h) of type (builtin_comp2 f h) -> (builtin_comp2 g h).

  $ catt features/suspension.catt
  [=^.^=] let comp2 = (!1 _builtin_comp  a b)
  [=I.I=] successfully defined term (!1builtin_comp2 a b) of type f -> h.
  [=^.^=] let id3 = (!2 _builtin_id  (!1 _builtin_id  (_builtin_id  x)))
  [=I.I=] successfully defined term (!2builtin_id (!1builtin_id (builtin_id x))) of type (!1builtin_id (builtin_id x)) -> (!1builtin_id (builtin_id x)).
  [=^.^=] let c = (_builtin_comp  a b)
  [=I.I=] successfully defined term (!1builtin_comp2 a b) of type f -> h.
  [=^.^=] coh whisk = (_builtin_comp  f h) -> (_builtin_comp  g h)
  [=I.I=] successfully defined whisk.
  [=^.^=] let test = (whisk  (_builtin_comp  a b) k)
  [=I.I=] successfully defined term (whisk (!1builtin_comp2 a b) k) of type (builtin_comp2 f k) -> (builtin_comp2 h k).

  $ catt features/verbosity.catt
  [=^.^=] coh comp3 = x -> w
  [=I.I=] inferring constraints for context:  {x: *} {y: *} (f: _ty0 | x -> y) {z: *} (g: _ty1 | y -> z) {w: *} (h: _ty2 | z -> w).
  [=I.I=] context elaborated to  {x: *} {y: *} (f: * | x -> y) {z: *} (g: * | y -> z) {w: *} (h: * | z -> w).
  [=I.I=] inferring constraints for type: _ty3 | x -> w.
  [=I.I=] type elaborated to * | x -> w.
  [=I.I=] checking coherence: comp3.
  [=I.I=] successfully defined comp3.
  [=^.^=] let sq = (_builtin_comp  f f)
  [=I.I=] inferring constraints for context:  {x: *} (f: _ty4 | x -> x).
  [=I.I=] context elaborated to  {x: *} (f: * | x -> x).
  [=I.I=] checking term: (builtin_comp2 .2 .4).
  [=I.I=] inferring constraints for term: (builtin_comp2 f f).
  [=I.I=] term elaborated to (builtin_comp2 f f).
  [=I.I=] checking term: (builtin_comp2 f f).
  [=I.I=] successfully defined term (builtin_comp2 f f) of type * | x -> x.
  [=^.^=] let cbd = (_builtin_comp  f (_builtin_comp  f f))
  [=I.I=] inferring constraints for context:  {x: *} (f: _ty8 | x -> x).
  [=I.I=] context elaborated to  {x: *} (f: * | x -> x).
  [=I.I=] checking term: (builtin_comp2 .2 .4).
  [=I.I=] checking term: (builtin_comp2 .2 .4).
  [=I.I=] inferring constraints for term: (builtin_comp2 f (builtin_comp2 f f)).
  [=I.I=] term elaborated to (builtin_comp2 f (builtin_comp2 f f)).
  [=I.I=] inferring constraints for context:  {x: *} (f: _ty15 | x -> x).
  [=I.I=] context elaborated to  {x: *} (f: * | x -> x).
  [=I.I=] inferring constraints for type: _ty16 | x -> x.
  [=I.I=] type elaborated to * | x -> x.
  [=I.I=] checking type: * | x -> x.
  [=I.I=] checking term: (builtin_comp2 f (builtin_comp2 f f)).
  [=I.I=] successfully defined term (builtin_comp2 f (builtin_comp2 f f)) of type * | x -> x.
  [=^.^=] coh simpl = (sq  (_builtin_id  x)) -> (_builtin_id  x)
  [=I.I=] inferring constraints for context:  (x: *).
  [=I.I=] context elaborated to  (x: *).
  [=I.I=] checking coherence: builtin_id.
  [=I.I=] checking term: (builtin_id .0).
  [=I.I=] checking coherence: builtin_id.
  [=I.I=] checking term: (builtin_id .0).
  [=I.I=] inferring constraints for type: _ty18 | (sq (builtin_id x)) -> (builtin_id x).
  [=I.I=] type elaborated to * | x -> x | (sq (builtin_id x)) -> (builtin_id x).
  [=I.I=] checking coherence: simpl.
  [=I.I=] successfully defined simpl.
  [=^.^=] check (_builtin_comp  (sq  f) (cbd  f))
  [=I.I=] inferring constraints for context:  {x: *} (f: _ty19 | x -> x).
  [=I.I=] context elaborated to  {x: *} (f: * | x -> x).
  [=I.I=] checking term: (builtin_comp2 .2 .4).
  [=I.I=] inferring constraints for term: (builtin_comp2 (sq f) (cbd f)).
  [=I.I=] term elaborated to (builtin_comp2 (sq f) (cbd f)).
  [=I.I=] checking term: (builtin_comp2 (sq f) (cbd f)).
  [=I.I=] valid term (builtin_comp2 (sq f) (cbd f)) of type * | x -> x.

  $ catt features/let-in.catt
  [=^.^=] let id2 = (_builtin_id  (_builtin_id  x))
  [=I.I=] successfully defined term (!1builtin_id (builtin_id x)) of type (builtin_id x) -> (builtin_id x).
  [=^.^=] let a = let i = (id2  x) in i
  [=I.I=] successfully defined term (id2 x) of type (builtin_id x) -> (builtin_id x).
  [=^.^=] let f = let i = (_builtin_id  x) in let j = (_builtin_id  i) in j
  [=I.I=] successfully defined term (!1builtin_id (builtin_id x)) of type (builtin_id x) -> (builtin_id x).

  $ catt features/functorialisation.catt
  [=^.^=] let whiskl = (_builtin_comp  [a] h)
  [=I.I=] successfully defined term (builtin_comp2 [a] h) of type (builtin_comp2 f h) -> (builtin_comp2 g h).
  [=^.^=] let whiskr = (_builtin_comp  f [a])
  [=I.I=] successfully defined term (builtin_comp2 f [a]) of type (builtin_comp2 f g) -> (builtin_comp2 f h).
  [=^.^=] let whiskl2 = (whiskl  [m] h)
  [=I.I=] successfully defined term (whiskl [m] h) of type (builtin_comp2 [a] h) -> (builtin_comp2 [a'] h).
  [=^.^=] let comp302 = (_builtin_comp  [[m]] [c])
  [=I.I=] successfully defined term (builtin_comp2 [[m]] [c]) of type (builtin_comp2 [a] [c]) -> (builtin_comp2 [b] [c]).
  [=^.^=] let comp303 = (_builtin_comp  [[m]] [[n]])
  [=I.I=] successfully defined term (builtin_comp2 [[m]] [[n]]) of type (builtin_comp2 [a] [c]) -> (builtin_comp2 [b] [d]).
  [=^.^=] let comp504 = (comp303  [[F]] [C])
  [=I.I=] successfully defined term (comp303 [[F]] [C]) of type (builtin_comp2 [[[A]]] [[[C]]]) -> (builtin_comp2 [[[B]]] [[[C]]]).
  [=^.^=] let comp-biased = (_builtin_comp  (_builtin_comp  f g) h)
  [=I.I=] successfully defined term (builtin_comp2 (builtin_comp2 f g) h) of type x -> w.
  [=^.^=] check (comp-biased  f [a] h)
  [=I.I=] valid term (comp-biased f [a] h) of type (builtin_comp2 (builtin_comp2 f g) h) -> (builtin_comp2 (builtin_comp2 f g') h).

  $ catt features/opposites.catt
  [=^.^=] let opcomp = op_{1}((_builtin_comp  g f))
  [=I.I=] successfully defined term (builtin_comp2_op{1} z y g x f) of type x -> z.
  [=^.^=] let opwhisk = op_{1}((_builtin_comp  g [a]))
  [=I.I=] successfully defined term (builtin_comp2_func[1]_op{1} z y g x f f' a) of type (builtin_comp2_op{1} x y f z g) -> (builtin_comp2_op{1} x y f' z g).
  [=^.^=] coh test = (_builtin_comp  f g) -> (_builtin_comp  f'' g'')
  [=I.I=] successfully defined test.
  [=^.^=] let optest1 = op_{1}((test  c d a b))
  [=I.I=] successfully defined term (test_op{1} z y g g' c g'' d x f f' a f'' b) of type (builtin_comp2_op{1} z y g x f) -> (builtin_comp2_op{1} z y g'' x f'').
  [=^.^=] let optest2 = op_{2}((test  b a d c))
  [=I.I=] successfully defined term (test_op{2} x y f'' f' b f a z g'' g' d g c) of type (builtin_comp2_op{2} x y f z g) -> (builtin_comp2_op{2} x y f'' z g'').
  [=^.^=] let optest12 = op_{1,2}((test  d c b a))
  [=I.I=] successfully defined term (test_op{1,2} z y g'' g' d g c x f'' f' b f a) of type (builtin_comp2_op{1,2} z y g x f) -> (builtin_comp2_op{1,2} z y g'' x f'').
  [=^.^=] let nested1 = op_{1}((_builtin_comp  [(_builtin_comp  c d)] [(_builtin_comp  a b)]))
  [=I.I=] successfully defined term (builtin_comp2_func[1 1]_op{1} z y g g'' (!1builtin_comp2_op{1} z y g g' c g'' d) x f f'' (!1builtin_comp2_op{1} y x f f' a f'' b)) of type (builtin_comp2_op{1} x y f z g) -> (builtin_comp2_op{1} x y f'' z g'').
  [=^.^=] let nested2 = op_{2}((_builtin_comp  [(_builtin_comp  b a)] [(_builtin_comp  d c)]))
  [=I.I=] successfully defined term (builtin_comp2_func[1 1]_op{2} x y f'' f (!1builtin_comp2_op{2} x y f'' f' b f a) z g'' g (!1builtin_comp2_op{2} y z g'' g' d g c)) of type (builtin_comp2_op{1} x y f z g) -> (builtin_comp2_op{1} x y f'' z g'').
  [=^.^=] let nested12 = op_{1,2}((_builtin_comp  [(_builtin_comp  d c)] [(_builtin_comp  b a)]))
  [=I.I=] successfully defined term (builtin_comp2_func[1 1]_op{1,2} z y g'' g (!1builtin_comp2_op{1,2} z y g'' g' d g c) x f'' f (!1builtin_comp2_op{1,2} y x f'' f' b f a)) of type (builtin_comp2_op{1} x y f z g) -> (builtin_comp2_op{1} x y f'' z g'').
  [=^.^=] coh assoc = (_builtin_comp  f (_builtin_comp  g h)) -> (_builtin_comp  (_builtin_comp  f g) h)
  [=I.I=] successfully defined assoc.
  [=^.^=] coh assoc_susp = (_builtin_comp  f (_builtin_comp  g h)) -> (_builtin_comp  (_builtin_comp  f g) h)
  [=I.I=] successfully defined assoc_susp.
  [=^.^=] let test = (_builtin_id  op_{3}((assoc_susp  f g h)))
  [=I.I=] successfully defined term (!3builtin_id p q x w (!1builtin_comp2_op{3} p q x z (!1builtin_comp2_op{3} p q x y f z g) w h) (!1builtin_comp2_op{3} p q x y f w (!1builtin_comp2_op{3} p q y z g w h)) (assoc_susp_op{3} p q x y f z g w h)) of type (assoc_susp_op{3} p q x y f z g w h) -> (assoc_susp_op{3} p q x y f z g w h).

  $ catt features/inverses.catt
  [=^.^=] let id_inv = I((_builtin_id  x))
  [=I.I=] successfully defined term (builtin_id x) of type x -> x.
  [=^.^=] coh assoc = (_builtin_comp  (_builtin_comp  f g) h) -> (_builtin_comp  f (_builtin_comp  g h))
  [=I.I=] successfully defined assoc.
  [=^.^=] coh unbiase = (_builtin_comp  f (_builtin_comp  g h)) -> (_builtin_comp  f g h)
  [=I.I=] successfully defined unbiase.
  [=^.^=] coh unitl = (_builtin_comp  (_builtin_id  x) f) -> f
  [=I.I=] successfully defined unitl.
  [=^.^=] coh 21comp = (_builtin_comp  f k) -> (_builtin_comp  h l)
  [=I.I=] successfully defined 21comp.
  [=^.^=] coh 2whisk = (_builtin_comp  f k) -> (_builtin_comp  h k)
  [=I.I=] successfully defined 2whisk.
  [=^.^=] let assoc_inv = I((assoc  f g h))
  [=I.I=] successfully defined term (assoc^-1 f g h) of type (builtin_comp2 f (builtin_comp2 g h)) -> (builtin_comp2 (builtin_comp2 f g) h).
  [=^.^=] let unbiase_inv = I((unbiase  f g h))
  [=I.I=] successfully defined term (unbiase^-1 f g h) of type (builtin_comp3 f g h) -> (builtin_comp2 f (builtin_comp2 g h)).
  [=^.^=] let unitl_inv = I((unitl  f))
  [=I.I=] successfully defined term (unitl^-1 f) of type f -> (builtin_comp2 (builtin_id x) f).
  [=^.^=] let assoc_unbiase_inv = I((_builtin_comp  (assoc  f f f) (unbiase  f f f)))
  [=I.I=] successfully defined term (!1builtin_comp2 (unbiase^-1 f f f) (assoc^-1 f f f)) of type (builtin_comp3 f f f) -> (builtin_comp2 (builtin_comp2 f f) f).
  [=^.^=] let id_id_inv = I((_builtin_comp  (_builtin_id  x) (_builtin_id  x)))
  [=I.I=] successfully defined term (builtin_comp2_op{1} (builtin_id x) (builtin_id x)) of type x -> x.
  [=^.^=] check I((_builtin_comp  (_builtin_id  x) [(_builtin_comp  (assoc  f f f) (unbiase  f f f))] (_builtin_id  x)))
  [=I.I=] valid term (builtin_comp3_func[1]_op{2} (builtin_id x) (!1builtin_comp2 (unbiase^-1 f f f) (assoc^-1 f f f)) (builtin_id x)) of type (builtin_comp3_op{2} (builtin_id x) (builtin_comp3 f f f) (builtin_id x)) -> (builtin_comp3_op{2} (builtin_id x) (builtin_comp2 (builtin_comp2 f f) f) (builtin_id x)).
  [=^.^=] check I((21comp  (assoc  f f f) (unbiase  f f f) (assoc  f f f)))
  [=I.I=] valid term (21comp_op{2} (unbiase^-1 f f f) (assoc^-1 f f f) (assoc^-1 f f f)) of type (builtin_comp2_op{2} (builtin_comp3 f f f) (builtin_comp2 f (builtin_comp2 f f))) -> (builtin_comp2_op{2} (builtin_comp2 (builtin_comp2 f f) f) (builtin_comp2 (builtin_comp2 f f) f)).
  [=^.^=] check I((2whisk  (_builtin_id  f) (_builtin_id  f) f))
  [=I.I=] valid term (2whisk_op{2} (!1builtin_id f) (!1builtin_id f) f) of type (builtin_comp2_op{2} f f) -> (builtin_comp2_op{2} f f).
  [=^.^=] check I((_builtin_comp  [(_builtin_comp  (assoc  (_builtin_id  f) (_builtin_id  f) (_builtin_id  f)) (unbiase  (_builtin_id  f) (_builtin_id  f) (_builtin_id  f)))] (_builtin_id  f)))
  [=I.I=] valid term (!1builtin_comp2 [(!2builtin_comp2 (!1unbiase^-1 (!1builtin_id f) (!1builtin_id f) (!1builtin_id f)) (!1assoc^-1 (!1builtin_id f) (!1builtin_id f) (!1builtin_id f)))] (!1builtin_id f)) of type (!1builtin_comp2 (!1builtin_comp3 (!1builtin_id f) (!1builtin_id f) (!1builtin_id f)) (!1builtin_id f)) -> (!1builtin_comp2 (!1builtin_comp2 (!1builtin_comp2 (!1builtin_id f) (!1builtin_id f)) (!1builtin_id f)) (!1builtin_id f)).
  [=^.^=] check I((_builtin_comp  [(_builtin_comp  (assoc  f f f) (unbiase  f f f))] (_builtin_comp  (_builtin_id  x) I((_builtin_id  x))) [I((_builtin_comp  (_builtin_id  g) (_builtin_id  g)))] (_builtin_id  y)))
  [=I.I=] valid term (builtin_comp4_func[1 1]_op{2} (!1builtin_comp2 (unbiase^-1 f f f) (assoc^-1 f f f)) (builtin_comp2 (builtin_id x) (builtin_id x)) (!1builtin_comp2 (!1builtin_id g) (!1builtin_id g)) (builtin_id y)) of type (builtin_comp4_op{2} (builtin_comp3 f f f) (builtin_comp2 (builtin_id x) (builtin_id x)) g (builtin_id y)) -> (builtin_comp4_op{2} (builtin_comp2 (builtin_comp2 f f) f) (builtin_comp2 (builtin_id x) (builtin_id x)) g (builtin_id y)).
  [=^.^=] check I((assoc  x y f z g w h))
  [=I.I=] valid term (assoc^-1 f g h) of type (builtin_comp2 f (builtin_comp2 g h)) -> (builtin_comp2 (builtin_comp2 f g) h).
  [=^.^=] check U((assoc  f g h))
  [=I.I=] valid term (assoc_Unit f g h) of type (!1builtin_comp2 (builtin_comp2 (builtin_comp2 f g) h) (builtin_comp2 f (builtin_comp2 g h)) (assoc f g h) (assoc^-1 f g h)) -> (!1builtin_id (builtin_comp2 (builtin_comp2 f g) h)).
  [=^.^=] check U((_builtin_comp  (_builtin_id  f) (_builtin_id  f)))
  [=I.I=] valid term (!2builtin_comp3 (vertical_grouping (!1builtin_id f) (!1builtin_id f) (!1builtin_id f) (!1builtin_id f)) (unbiased_comp_red [(!1builtin_telescope2 (!1builtin_id_Unit f) (!1builtin_id_Unit f))]) (unbiased_unitor f)) of type (!1builtin_comp2 (!1builtin_comp2 (!1builtin_id f) (!1builtin_id f)) (!1builtin_comp2 (!1builtin_id f) (!1builtin_id f))) -> (!1builtin_id f).
  [=^.^=] check U((_builtin_comp  [(_builtin_id  f)] [(_builtin_id  g)]))
  [=I.I=] valid term (!2builtin_comp3 (vertical_grouping (!1builtin_id f) (!1builtin_id f) (!1builtin_id g) (!1builtin_id g)) (unbiased_comp_red [(!1builtin_telescope1 (!1builtin_id_Unit f))] [(!1builtin_telescope1 (!1builtin_id_Unit g))]) (unbiased_unitor f g)) of type (!1builtin_comp2 (builtin_comp2 [(!1builtin_id f)] [(!1builtin_id g)]) (builtin_comp2_func[1 1]_op{2} (!1builtin_id f) (!1builtin_id g))) -> (!1builtin_id (builtin_comp2 f g)).
  [=^.^=] check U((_builtin_comp  (assoc  f f f) (unbiase  f f f)))
  [=I.I=] valid term (!2builtin_comp3 (vertical_grouping (assoc f f f) (unbiase f f f) (unbiase^-1 f f f) (assoc^-1 f f f)) (unbiased_comp_red [(!1builtin_telescope2 (assoc_Unit f f f) (unbiase_Unit f f f))]) (unbiased_unitor (builtin_comp2 (builtin_comp2 f f) f))) of type (!1builtin_comp2 (!1builtin_comp2 (assoc f f f) (unbiase f f f)) (!1builtin_comp2 (unbiase^-1 f f f) (assoc^-1 f f f))) -> (!1builtin_id (builtin_comp2 (builtin_comp2 f f) f)).
  [=^.^=] check U((_builtin_comp  (assoc  f f g) (_builtin_id  (_builtin_comp  f (_builtin_comp  f g))) (unbiase  f f g) I((unbiase  f f g))))
  [=I.I=] valid term (!2builtin_comp3 (vertical_grouping (assoc f f g) (!1builtin_id (builtin_comp2 f (builtin_comp2 f g))) (unbiase f f g) (unbiase^-1 f f g) (unbiase f f g) (unbiase^-1 f f g) (!1builtin_id (builtin_comp2 f (builtin_comp2 f g))) (assoc^-1 f f g)) (unbiased_comp_red [(!1builtin_telescope4 (assoc_Unit f f g) (!1builtin_id_Unit (builtin_comp2 f (builtin_comp2 f g))) (unbiase_Unit f f g) (unbiase^-1_Unit f f g))]) (unbiased_unitor (builtin_comp2 (builtin_comp2 f f) g))) of type (!1builtin_comp2 (!1builtin_comp4 (assoc f f g) (!1builtin_id (builtin_comp2 f (builtin_comp2 f g))) (unbiase f f g) (unbiase^-1 f f g)) (!1builtin_comp4 (unbiase f f g) (unbiase^-1 f f g) (!1builtin_id (builtin_comp2 f (builtin_comp2 f g))) (assoc^-1 f f g))) -> (!1builtin_id (builtin_comp2 (builtin_comp2 f f) g)).
  [=^.^=] check U((21comp  (assoc  f f f) (unbiase  f f f) (assoc  g g g)))
  [=I.I=] valid term (!2builtin_comp3 (vertical_grouping (assoc f f f) (unbiase f f f) (unbiase^-1 f f f) (assoc^-1 f f f) (assoc g g g) (assoc^-1 g g g)) (unbiased_comp_red [(!1builtin_telescope2 (assoc_Unit f f f) (unbiase_Unit f f f))] [(!1builtin_telescope1 (assoc_Unit g g g))]) (unbiased_unitor (builtin_comp2 (builtin_comp2 f f) f) (builtin_comp2 (builtin_comp2 g g) g))) of type (!1builtin_comp2 (21comp (assoc f f f) (unbiase f f f) (assoc g g g)) (21comp_op{2} (unbiase^-1 f f f) (assoc^-1 f f f) (assoc^-1 g g g))) -> (!1builtin_id (builtin_comp2 (builtin_comp2 (builtin_comp2 f f) f) (builtin_comp2 (builtin_comp2 g g) g))).

  $ catt features/naturality.catt
  [=^.^=] let idf = (_builtin_id  [f])
  [=I.I=] successfully defined term (builtin_id [f]) of type (builtin_comp2 (builtin_id x) f) -> (builtin_comp2 f (builtin_id y)).
  [=^.^=] coh whiskl = (_builtin_comp  f g) -> (_builtin_comp  f h)
  [=I.I=] successfully defined whiskl.
  [=^.^=] let whisklf = (whiskl  [a] b)
  [=I.I=] successfully defined term (whiskl [a] b) of type (!1builtin_comp2 (whiskl f b) (builtin_comp2 [a] k)) -> (!1builtin_comp2 (builtin_comp2 [a] h) (whiskl g b)).
  [=^.^=] let whisklf = (whiskl  f [m])
  [=I.I=] successfully defined term (whiskl f [m]) of type (whiskl f b) -> (whiskl f c).
  [=^.^=] coh assoc = (_builtin_comp  (_builtin_comp  f g) h) -> (_builtin_comp  f (_builtin_comp  g h))
  [=I.I=] successfully defined assoc.
  [=^.^=] let nat_assoc = (assoc  [a] [b] [c])
  [=I.I=] successfully defined term (assoc [a] [b] [c]) of type (!1builtin_comp2 (assoc f g h) (builtin_comp2 [a] [(builtin_comp2 [b] [c])])) -> (!1builtin_comp2 (builtin_comp2 [(builtin_comp2 [a] [b])] [c]) (assoc f' g' h')).
  [=^.^=] let whiskL = (_builtin_comp  f [a])
  [=I.I=] successfully defined term (builtin_comp2 f [a]) of type (builtin_comp2 f g) -> (builtin_comp2 f h).
  [=^.^=] let nat_assoc = (assoc  [a] [[B]] [c])
  [=I.I=] successfully defined term (assoc [a] [[B]] [c]) of type (!2builtin_comp2 (assoc [a] [b] [c]) (!1builtin_comp2 [(builtin_comp2 [[(builtin_comp2 [a] [[B]])]] [c])] (assoc f' g' h'))) -> (!2builtin_comp2 (!1builtin_comp2 (assoc f g h) [(builtin_comp2 [a] [[(builtin_comp2 [[B]] [c])]])]) (assoc [a] [b'] [c])).
  [=^.^=] let exch = (whiskl  [a] b)
  [=I.I=] successfully defined term (whiskl [a] b) of type (!1builtin_comp2 (whiskl f b) (builtin_comp2 [a] g')) -> (!1builtin_comp2 (builtin_comp2 [a] g) (whiskl f' b)).
  [=^.^=] coh whiskl3 = (_builtin_comp  f [a]) -> (_builtin_comp  f [b])
  [=I.I=] successfully defined whiskl3.
  [=^.^=] let nat_whiskl3 = (whiskl3  [c] m)
  [=I.I=] successfully defined term (whiskl3 [c] m) of type (!2builtin_comp2 (@!1builtin_comp2 _ _ [_] _ (whiskl3 f m) _ (builtin_comp2 [c] h)) (builtin_comp2_func[1] [c] b)) -> (!2builtin_comp2 (builtin_comp2_func[1] [c] a) (@!1builtin_comp2 _ _ _ _ [_] _ (whiskl3 f' m))).
  [=^.^=] coh whiskl4 = (_builtin_comp  f [[[p]]]) -> (_builtin_comp  f [[[p]]])
  [=I.I=] successfully defined whiskl4.
  [=^.^=] coh id2 = (_builtin_comp  (_builtin_id  x) (_builtin_id  x) (_builtin_id  x)) -> (_builtin_comp  (_builtin_id  x))
  [=I.I=] successfully defined id2.
  [=^.^=] let nat_id2 = (id2  [f])
  [=I.I=] successfully defined term (id2 [f]) of type (!1builtin_comp2 (builtin_comp2 [(id2 x)] f) (@builtin_comp1 [_] [_] [(builtin_id [f])])) -> (!1builtin_comp2 (@builtin_comp3 [_] [_] [(builtin_id [f])] [_] [(builtin_id [f])] [_] [(builtin_id [f])]) (builtin_comp2 f [(id2 y)])).
  [=^.^=] coh vcompwhisk = (_builtin_comp  (_builtin_id  x) f g) -> (_builtin_comp  f (_builtin_id  y) k)
  [=I.I=] successfully defined vcompwhisk.
  [=^.^=] let vcompwhisk2 = (vcompwhisk  f (_builtin_id  g) (_builtin_id  g))
  [=I.I=] successfully defined term (vcompwhisk f (!1builtin_id g) (!1builtin_id g)) of type (builtin_comp3 (builtin_id x) f g) -> (builtin_comp3 f (builtin_id y) g).
  [=^.^=] let nat_vcompwhisk = (vcompwhisk2  [a] [c])
  [=I.I=] successfully defined term (vcompwhisk2 [a] [c]) of type (!1builtin_comp2 (vcompwhisk f (!1builtin_id g) (!1builtin_id g)) (builtin_comp3 [a] (builtin_id y) [c])) -> (!1builtin_comp2 (builtin_comp3 (builtin_id x) [a] [c]) (vcompwhisk f' (!1builtin_id g') (!1builtin_id g'))).
  [=^.^=] let triangle1 = (_builtin_comp  x [ym] [fm] z [gm])
  [=I.I=] successfully defined term (@builtin_comp2 _ [_] [fm] _ [gm]) of type (builtin_comp2 f g) -> (builtin_comp2 f' g').
  [=^.^=] let triangle2 = (_builtin_comp  [xm] y [fm] [zm] [gm])
  [=I.I=] successfully defined term (@builtin_comp2 [_] _ [fm] [_] [gm]) of type (builtin_comp2 (builtin_comp2 f g) zm) -> (builtin_comp2 xm (builtin_comp2 f' g')).
  [=^.^=] let triangle1_bis = (@_builtin_comp  _ [_] [fm] _ [gm])
  [=I.I=] successfully defined term (@builtin_comp2 _ [_] [fm] _ [gm]) of type (builtin_comp2 f g) -> (builtin_comp2 f' g').
  [=^.^=] let triangle2_bis = (@_builtin_comp  [_] _ [fm] [_] [gm])
  [=I.I=] successfully defined term (@builtin_comp2 [_] _ [fm] [_] [gm]) of type (builtin_comp2 (builtin_comp2 f g) zm) -> (builtin_comp2 xm (builtin_comp2 f' g')).
  [=^.^=] coh example = (_builtin_comp  f k (_builtin_id  z)) -> (_builtin_comp  h l)
  [=I.I=] successfully defined example.
  [=^.^=] let ex1 = (@example  _ _ _ [_] [am] [_] [bm] _ _ [_] [cm])
  [=I.I=] successfully defined term (@example _ _ _ [_] [am] [_] [bm] _ _ [_] [cm]) of type (!1builtin_comp2 (example a b c) (builtin_comp2 [hm] [lm])) -> (example a+ b+ c+).
  [=^.^=] let ex2 = (@example  _ _ _ [_] [am] [_] [bm] _ [_] _ [cm])
  [=I.I=] successfully defined term (@example _ _ _ [_] [am] [_] [bm] _ [_] _ [cm]) of type (!1builtin_comp2 (example a b c) (builtin_comp2 [hm] l)) -> (!1builtin_comp2 (builtin_comp3 f [km] (builtin_id z)) (example a+ b+ c+)).
  [=^.^=] let ex3 = (@example  _ _ _ [_] [am] [_] [bm] _ [_] [_] [cm])
  [=I.I=] successfully defined term (@example _ _ _ [_] [am] [_] [bm] _ [_] [_] [cm]) of type (!1builtin_comp2 (example a b c) (builtin_comp2 [hm] [lm])) -> (!1builtin_comp2 (builtin_comp3 f [km] (builtin_id z)) (example a+ b+ c+)).

  $ catt --keep-going fails/notps.catt
  [=^.^=] coh fail1 = x -> x
  [=X.X=] The following context is not a pasting scheme:
   {x: *} (f: x -> x)
  [=^.^=] coh fail2 = x -> z
  [=X.X=] The following context is not a pasting scheme:
   {x: *} {y: *} (f: x -> y) {z: *} (g: z -> y)
  [=^.^=] coh fail3 = x -> w
  [=X.X=] The following context is not a pasting scheme:
   {x: *} {y: *} (f: x -> y) {z: *} {w: *} (g: z -> w)
  [=^.^=] coh fail4 = x -> z
  [=X.X=] The following context is not a pasting scheme:
   {x: *} {y: *} {z: *} (f: x -> y) (g: y -> z)
  [=^.^=] coh fail5 = x -> z
  [=X.X=] The following context is not a pasting scheme:
   {x: *} {y: *} {f: x -> y} {z: *} {g: y -> z} (a: (builtin_comp2 f g) -> (builtin_comp2 f g))

  $ catt --keep-going fails/doubledvars.catt
  [=^.^=] let fail1 = (_builtin_id  x)
  [=X.X=] The following context is invalid because variable x is repeated:
   (x: *) (x: *)
  [=^.^=] coh fail2 = x -> x
  [=X.X=] The following context is invalid because variable x is repeated:
   {x: *} {x: *} (f: x -> x)

  $ catt --keep-going fails/invalidcoherences.catt
  [=^.^=] coh fail1 = x -> x
  [=X.X=] The coherence fail1 is not valid for the following reason:
  type .0 -> .0 not algebraic in pasting scheme  {.0: *} {.1: *} (.2: .0 -> .1)
  [=^.^=] coh fail2 = x -> z
  [=X.X=] The coherence fail2 is not valid for the following reason:
  type .0 -> .5 not algebraic in pasting scheme  {.0: *} {.1: *} {.2: .0 -> .1} {.3: .0 -> .1} (.4: .2 -> .3) {.5: *} {.6: .1 -> .5} {.7: .1 -> .5} (.8: .6 -> .7)
  [=^.^=] coh fail3 = f -> g
  [=X.X=] The coherence fail3 is not valid for the following reason:
  type .2 -> .3 not algebraic in pasting scheme  {.0: *} {.1: *} {.2: .0 -> .1} {.3: .0 -> .1} (.4: .2 -> .3) {.5: *} {.6: .1 -> .5} {.7: .1 -> .5} (.8: .6 -> .7)

  $ catt --keep-going fails/invalidtypes.catt
  [=^.^=] coh fail1 = x -> f
  [=X.X=] The constraints generated for the type: x -> f could not be solved for the following reason:
  could not unify * and x -> y
  [=^.^=] let fail2 = (_builtin_id  x)
  [=X.X=] The constraints generated for the context:  {x: *} {y: *} {f: x -> y} (g: x -> f) could not be solved for the following reason:
  could not unify * and x -> y
  [=^.^=] coh fail3 = x -> y
  [=X.X=] The constraints generated for the context:  {x: *} {y: *} {f: x -> y} (g: x -> f) could not be solved for the following reason:
  could not unify * and x -> y
  [=^.^=] let fail4 = (_builtin_comp  f g)
  [=X.X=] The constraints generated for the type: x -> f could not be solved for the following reason:
  could not unify * and x -> y

  $ catt --keep-going fails/wrongapplication.catt
  [=^.^=] let fail1 = (_builtin_comp  f g)
  [=X.X=] The constraints generated for the term: (builtin_comp2 f g) could not be solved for the following reason:
  could not unify x and y
  [=^.^=] coh whisk = (_builtin_comp  f h) -> (_builtin_comp  g h)
  [=I.I=] successfully defined whisk.
  [=^.^=] let fail2 = (whisk  f b)
  [=X.X=] The constraints generated for the term: (whisk f b) could not be solved for the following reason:
  could not unify * and _tm13 -> _tm12
  [=^.^=] let fail3 = (_builtin_comp  [f] b)
  [=X.X=] The constraints generated for the term: (builtin_comp2 [f] b) could not be solved for the following reason:
  could not unify * and _tm18 -> _tm17
  [=^.^=] let fail4 = (_builtin_comp  [f] g)
  [=X.X=] The constraints generated for the term: (builtin_comp2 [f] g) could not be solved for the following reason:
  could not unify * and _tm23 -> _tm22

  $ catt --keep-going fails/invalidnaturality.catt
  [=^.^=] let fail1 = (@_builtin_comp  x [f] f x f)
  [=X.X=] Could not compute the transformation of coherence: builtin_comp2 for the following reason:
  list of functorialised arguments is not closed
  [=^.^=] let whisk = (_builtin_comp  [a] h)
  [=I.I=] successfully defined term (builtin_comp2 [a] h) of type (builtin_comp2 f h) -> (builtin_comp2 g h).
  [=^.^=] let fail2 = (@whisk  [_] [_] [_] [_] [m] _ [h])
  [=X.X=] Could not compute the transformation of term: whisk for the following reason:
  higher-dimensional transformations in depth >= 0 are not yet supported

  $ catt --keep-going fails/uninferrable.catt
  [=^.^=] let fail1 = (_builtin_comp  (_builtin_id  _) (_builtin_id  _))
  [=X.X=] Incomplete constraints: some of the meta-variable could not be resolved in the following term: (builtin_comp2 (builtin_id _tm1) (builtin_id _tm1))
  [=^.^=] coh fail2 = (_builtin_comp  (_builtin_id  _) _) -> f
  [=X.X=] Incomplete constraints: some of the meta-variable could not be resolved in the following coherence: fail2

  $ catt --keep-going fails/invalidinverse.catt
  [=^.^=] let fail1 = I((_builtin_comp  f g))
  [=X.X=] Could not compute the inverse of term: (builtin_comp2 f g) for the following reason:
  term f is not invertible
  [=^.^=] let fail1 = I((_builtin_comp  [a] [(_builtin_id  g)]))
  [=X.X=] Could not compute the inverse of term: (builtin_comp2 [a] [(!1builtin_id g)]) for the following reason:
  term a is not invertible

  $ catt coverage/eckmann-hilton-unoptimized.catt
  [=^.^=] coh comp3 = x1 -> x4
  [=I.I=] successfully defined comp3.
  [=^.^=] coh comp4 = x1 -> x5
  [=I.I=] successfully defined comp4.
  [=^.^=] coh comp5 = x1 -> x6
  [=I.I=] successfully defined comp5.
  [=^.^=] coh comp6 = x1 -> x7
  [=I.I=] successfully defined comp6.
  [=^.^=] coh comp7 = x1 -> x8
  [=I.I=] successfully defined comp7.
  [=^.^=] coh comp8 = x1 -> x9
  [=I.I=] successfully defined comp8.
  [=^.^=] coh comp9 = x1 -> x10
  [=I.I=] successfully defined comp9.
  [=^.^=] coh comp10 = x1 -> x11
  [=I.I=] successfully defined comp10.
  [=^.^=] coh comp11 = x1 -> x12
  [=I.I=] successfully defined comp11.
  [=^.^=] coh comp12 = x1 -> x13
  [=I.I=] successfully defined comp12.
  [=^.^=] coh comp13 = x1 -> x14
  [=I.I=] successfully defined comp13.
  [=^.^=] coh focus2 = (_builtin_comp  (_builtin_comp  f1 f2) (_builtin_comp  f3 f4)) -> (comp3  f1 (_builtin_comp  f2 f3) f4)
  [=I.I=] successfully defined focus2.
  [=^.^=] coh focus3 = (_builtin_comp  (comp3  f1 f2 f3) (comp3  f4 f5 f6)) -> (comp5  f1 f2 (_builtin_comp  f3 f4) f5 f6)
  [=I.I=] successfully defined focus3.
  [=^.^=] coh focus5 = (_builtin_comp  (comp5  f1 f2 f3 f4 f5) (comp5  f6 f7 f8 f9 f10)) -> (comp9  f1 f2 f3 f4 (_builtin_comp  f5 f6) f7 f8 f9 f10)
  [=I.I=] successfully defined focus5.
  [=^.^=] coh focus6 = (_builtin_comp  (comp6  f1 f2 f3 f4 f5 f6) (comp6  f7 f8 f9 f10 f11 f12)) -> (comp11  f1 f2 f3 f4 f5 (_builtin_comp  f6 f7) f8 f9 f10 f11 f12)
  [=I.I=] successfully defined focus6.
  [=^.^=] coh focus7 = (_builtin_comp  (comp7  f1 f2 f3 f4 f5 f6 f7) (comp7  f8 f9 f10 f11 f12 f13 f14)) -> (comp13  f1 f2 f3 f4 f5 f6 (_builtin_comp  f7 f8) f9 f10 f11 f12 f13 f14)
  [=I.I=] successfully defined focus7.
  [=^.^=] coh focus2- = (comp3  f1 (_builtin_comp  f2 f3) f4) -> (_builtin_comp  (_builtin_comp  f1 f2) (_builtin_comp  f3 f4))
  [=I.I=] successfully defined focus2-.
  [=^.^=] coh focus3- = (comp5  f1 f2 (_builtin_comp  f3 f4) f5 f6) -> (_builtin_comp  (comp3  f1 f2 f3) (comp3  f4 f5 f6))
  [=I.I=] successfully defined focus3-.
  [=^.^=] coh focus3U = (_builtin_comp  (focus3  f1 f2 f3 f4 f5 f6) (focus3-  f1 f2 f3 f4 f5 f6)) -> (_builtin_id  (_builtin_comp  (comp3  f1 f2 f3) (comp3  f4 f5 f6)))
  [=I.I=] successfully defined focus3U.
  [=^.^=] coh focus3CU = (_builtin_comp  (focus3-  f1 f2 f3 f4 f5 f6) (focus3  f1 f2 f3 f4 f5 f6)) -> (_builtin_id  (comp5  f1 f2 (_builtin_comp  f3 f4) f5 f6))
  [=I.I=] successfully defined focus3CU.
  [=^.^=] coh id2@1 = (_builtin_comp  (_builtin_id  x) f) -> f
  [=I.I=] successfully defined id2@1.
  [=^.^=] coh id2@1- = f -> (_builtin_comp  (_builtin_id  x) f)
  [=I.I=] successfully defined id2@1-.
  [=^.^=] coh id2@2 = (_builtin_comp  f (_builtin_id  y)) -> f
  [=I.I=] successfully defined id2@2.
  [=^.^=] coh id2@2- = f -> (_builtin_comp  f (_builtin_id  y))
  [=I.I=] successfully defined id2@2-.
  [=^.^=] coh id3@2 = (comp3  f1 (_builtin_id  x2) f2) -> (_builtin_comp  f1 f2)
  [=I.I=] successfully defined id3@2.
  [=^.^=] coh id3@2- = (_builtin_comp  f1 f2) -> (comp3  f1 (_builtin_id  x2) f2)
  [=I.I=] successfully defined id3@2-.
  [=^.^=] coh id5@3 = (comp5  f1 f2 (_builtin_id  x3) f3 f4) -> (comp4  f1 f2 f3 f4)
  [=I.I=] successfully defined id5@3.
  [=^.^=] coh id5@3- = (comp4  f1 f2 f3 f4) -> (comp5  f1 f2 (_builtin_id  x3) f3 f4)
  [=I.I=] successfully defined id5@3-.
  [=^.^=] coh id5@3U = (_builtin_comp  (id5@3  f1 f2 f3 f4) (id5@3-  f1 f2 f3 f4)) -> (_builtin_id  (comp5  f1 f2 (_builtin_id  x3) f3 f4))
  [=I.I=] successfully defined id5@3U.
  [=^.^=] coh rew2@1 = (_builtin_comp  f1 g) -> (_builtin_comp  f2 g)
  [=I.I=] successfully defined rew2@1.
  [=^.^=] coh rew2@2 = (_builtin_comp  f g1) -> (_builtin_comp  f g2)
  [=I.I=] successfully defined rew2@2.
  [=^.^=] coh rew2A = (_builtin_comp  f1 g1) -> (_builtin_comp  f2 g2)
  [=I.I=] successfully defined rew2A.
  [=^.^=] coh rew3@2 = (comp3  f1 f2 f3) -> (comp3  f1 g2 f3)
  [=I.I=] successfully defined rew3@2.
  [=^.^=] coh rew3A = (comp3  f1 f2 f3) -> (comp3  g1 g2 g3)
  [=I.I=] successfully defined rew3A.
  [=^.^=] coh rew5@3 = (comp5  f1 f2 f3 f4 f5) -> (comp5  f1 f2 g3 f4 f5)
  [=I.I=] successfully defined rew5@3.
  [=^.^=] coh rew7@4 = (comp7  f1 f2 f3 f4 f5 f6 f7) -> (comp7  f1 f2 f3 g4 f5 f6 f7)
  [=I.I=] successfully defined rew7@4.
  [=^.^=] coh rew9@5 = (comp9  f1 f2 f3 f4 f5 f6 f7 f8 f9) -> (comp9  f1 f2 f3 f4 g5 f6 f7 f8 f9)
  [=I.I=] successfully defined rew9@5.
  [=^.^=] coh rew11@6 = (comp11  f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11) -> (comp11  f1 f2 f3 f4 f5 g6 f7 f8 f9 f10 f11)
  [=I.I=] successfully defined rew11@6.
  [=^.^=] coh rew13@7 = (comp13  f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13) -> (comp13  f1 f2 f3 f4 f5 f6 g7 f8 f9 f10 f11 f12 f13)
  [=I.I=] successfully defined rew13@7.
  [=^.^=] coh rew2compA = (_builtin_comp  (rew2A  a1 b1) (rew2A  a2 b2)) -> (rew2A  (_builtin_comp  a1 a2) (_builtin_comp  b1 b2))
  [=I.I=] successfully defined rew2compA.
  [=^.^=] coh rew2compA- = (rew2A  (_builtin_comp  a1 a2) (_builtin_comp  b1 b2)) -> (_builtin_comp  (rew2A  a1 b1) (rew2A  a2 b2))
  [=I.I=] successfully defined rew2compA-.
  [=^.^=] coh rew3comp@2 = (_builtin_comp  (rew3@2  f1 a f3) (rew3@2  f1 b f3)) -> (rew3@2  f1 (_builtin_comp  a b) f3)
  [=I.I=] successfully defined rew3comp@2.
  [=^.^=] coh rew3comp@2- = (rew3@2  f1 (_builtin_comp  a b) f3) -> (_builtin_comp  (rew3@2  f1 a f3) (rew3@2  f1 b f3))
  [=I.I=] successfully defined rew3comp@2-.
  [=^.^=] coh rew3compA = (_builtin_comp  (rew3A  a1 b1 c1) (rew3A  a2 b2 c2)) -> (rew3A  (_builtin_comp  a1 a2) (_builtin_comp  b1 b2) (_builtin_comp  c1 c2))
  [=I.I=] successfully defined rew3compA.
  [=^.^=] coh rew5comp@3 = (_builtin_comp  (rew5@3  f1 f2 a f4 f5) (rew5@3  f1 f2 b f4 f5)) -> (rew5@3  f1 f2 (_builtin_comp  a b) f4 f5)
  [=I.I=] successfully defined rew5comp@3.
  [=^.^=] coh rew7comp@4 = (_builtin_comp  (rew7@4  f1 f2 f3 a f5 f6 f7) (rew7@4  f1 f2 f3 b f5 f6 f7)) -> (rew7@4  f1 f2 f3 (_builtin_comp  a b) f5 f6 f7)
  [=I.I=] successfully defined rew7comp@4.
  [=^.^=] coh rew2idA = (rew2A  (_builtin_id  f) (_builtin_id  g)) -> (_builtin_id  (_builtin_comp  f g))
  [=I.I=] successfully defined rew2idA.
  [=^.^=] coh rew3id@2 = (rew3@2  f1 (_builtin_id  f2) f3) -> (_builtin_id  (comp3  f1 f2 f3))
  [=I.I=] successfully defined rew3id@2.
  [=^.^=] coh rew3id@2- = (_builtin_id  (comp3  f1 f2 f3)) -> (rew3@2  f1 (_builtin_id  f2) f3)
  [=I.I=] successfully defined rew3id@2-.
  [=^.^=] coh rew3idA = (rew3A  (_builtin_id  f1) (_builtin_id  f2) (_builtin_id  f3)) -> (_builtin_id  (comp3  f1 f2 f3))
  [=I.I=] successfully defined rew3idA.
  [=^.^=] coh rew5id@3 = (rew5@3  f1 f2 (_builtin_id  f3) f4 f5) -> (_builtin_id  (comp5  f1 f2 f3 f4 f5))
  [=I.I=] successfully defined rew5id@3.
  [=^.^=] coh rew7id@4 = (rew7@4  f1 f2 f3 (_builtin_id  f4) f5 f6 f7) -> (_builtin_id  (comp7  f1 f2 f3 f4 f5 f6 f7))
  [=I.I=] successfully defined rew7id@4.
  [=^.^=] coh rew2Aid@1 = (comp3  (id2@1-  f) (rew2A  (_builtin_id  (_builtin_id  x)) a) (id2@1  g)) -> a
  [=I.I=] successfully defined rew2Aid@1.
  [=^.^=] coh rew2Aid@1- = a -> (comp3  (id2@1-  f) (rew2A  (_builtin_id  (_builtin_id  x)) a) (id2@1  g))
  [=I.I=] successfully defined rew2Aid@1-.
  [=^.^=] coh rew2Aid@2 = (comp3  (id2@2-  f) (rew2A  a (_builtin_id  (_builtin_id  y))) (id2@2  g)) -> a
  [=I.I=] successfully defined rew2Aid@2.
  [=^.^=] coh rew2Aid@2- = a -> (comp3  (id2@2-  f) (rew2A  a (_builtin_id  (_builtin_id  y))) (id2@2  g))
  [=I.I=] successfully defined rew2Aid@2-.
  [=^.^=] coh rrew2A = (rew2A  a0 b0) -> (rew2A  a1 b1)
  [=I.I=] successfully defined rrew2A.
  [=^.^=] coh rrew3@2 = (rew3@2  f1 a f3) -> (rew3@2  f1 b f3)
  [=I.I=] successfully defined rrew3@2.
  [=^.^=] coh rrew3A = (rew3A  a1 b1 c1) -> (rew3A  a2 b2 c2)
  [=I.I=] successfully defined rrew3A.
  [=^.^=] coh rrew5@3 = (rew5@3  f1 f2 a f4 f5) -> (rew5@3  f1 f2 b f4 f5)
  [=I.I=] successfully defined rrew5@3.
  [=^.^=] coh rrew7@4 = (rew7@4  f1 f2 f3 a f5 f6 f7) -> (rew7@4  f1 f2 f3 b f5 f6 f7)
  [=I.I=] successfully defined rrew7@4.
  [=^.^=] coh rrew2compA = (_builtin_comp  (rrew2A  al1 bet1) (rrew2A  al2 bet2)) -> (rrew2A  (_builtin_comp  al1 al2) (_builtin_comp  bet1 bet2))
  [=I.I=] successfully defined rrew2compA.
  [=^.^=] coh rrew2idA = (rrew2A  (_builtin_id  a0) (_builtin_id  b0)) -> (_builtin_id  (rew2A  a0 b0))
  [=I.I=] successfully defined rrew2idA.
  [=^.^=] coh rrrew2A = (rrew2A  al0 bet0) -> (rrew2A  al1 bet1)
  [=I.I=] successfully defined rrrew2A.
  [=^.^=] coh id2@/1-/2-/ = (id2@1-  (_builtin_id  x)) -> (id2@2-  (_builtin_id  x))
  [=I.I=] successfully defined id2@/1-/2-/.
  [=^.^=] coh id2@/1-/2-/- = (id2@2-  (_builtin_id  x)) -> (id2@1-  (_builtin_id  x))
  [=I.I=] successfully defined id2@/1-/2-/-.
  [=^.^=] coh id2@/1/2/ = (id2@1  (_builtin_id  x)) -> (id2@2  (_builtin_id  x))
  [=I.I=] successfully defined id2@/1/2/.
  [=^.^=] coh id2@/1/2/- = (id2@2  (_builtin_id  x)) -> (id2@1  (_builtin_id  x))
  [=I.I=] successfully defined id2@/1/2/-.
  [=^.^=] coh id2@2@1U = (_builtin_comp  (id2@2  (_builtin_id  x)) (id2@1-  (_builtin_id  x))) -> (_builtin_id  (_builtin_comp  (_builtin_id  x) (_builtin_id  x)))
  [=I.I=] successfully defined id2@2@1U.
  [=^.^=] coh id2@2@1U- = (_builtin_id  (_builtin_comp  (_builtin_id  x) (_builtin_id  x))) -> (_builtin_comp  (id2@2  (_builtin_id  x)) (id2@1-  (_builtin_id  x)))
  [=I.I=] successfully defined id2@2@1U-.
  [=^.^=] coh id2@1@2U = (_builtin_comp  (id2@1  (_builtin_id  x)) (id2@2-  (_builtin_id  x))) -> (_builtin_id  (_builtin_comp  (_builtin_id  x) (_builtin_id  x)))
  [=I.I=] successfully defined id2@1@2U.
  [=^.^=] coh id2@1@2U- = (_builtin_id  (_builtin_comp  (_builtin_id  x) (_builtin_id  x))) -> (_builtin_comp  (id2@1  (_builtin_id  x)) (id2@2-  (_builtin_id  x)))
  [=I.I=] successfully defined id2@1@2U-.
  [=^.^=] coh id5@3F = (comp5  f1 f2 (_builtin_id  x3) f3 f4) -> (comp3  f1 (_builtin_comp  f2 f3) f4)
  [=I.I=] successfully defined id5@3F.
  [=^.^=] coh id5@3F- = (comp3  f1 (_builtin_comp  f2 f3) f4) -> (comp5  f1 f2 (_builtin_id  x3) f3 f4)
  [=I.I=] successfully defined id5@3F-.
  [=^.^=] coh id5@3FU = (_builtin_comp  (id5@3F  f1 f2 f3 f4) (id5@3F-  f1 f2 f3 f4)) -> (_builtin_id  (comp5  f1 f2 (_builtin_id  x3) f3 f4))
  [=I.I=] successfully defined id5@3FU.
  [=^.^=] coh id5@3FCU = (_builtin_comp  (id5@3F-  f1 f2 f3 f4) (id5@3F  f1 f2 f3 f4)) -> (_builtin_id  (comp3  f1 (_builtin_comp  f2 f3) f4))
  [=I.I=] successfully defined id5@3FCU.
  [=^.^=] coh id7@4F = (comp7  f1 f2 f3 (_builtin_id  x4) f4 f5 f6) -> (comp5  f1 f2 (_builtin_comp  f3 f4) f5 f6)
  [=I.I=] successfully defined id7@4F.
  [=^.^=] coh id9@5F = (comp9  f1 f2 f3 f4 (_builtin_id  x5) f5 f6 f7 f8) -> (comp7  f1 f2 f3 (_builtin_comp  f4 f5) f6 f7 f8)
  [=I.I=] successfully defined id9@5F.
  [=^.^=] coh id11@6F = (comp11  f1 f2 f3 f4 f5 (_builtin_id  x6) f6 f7 f8 f9 f10) -> (comp9  f1 f2 f3 f4 (_builtin_comp  f5 f6) f7 f8 f9 f10)
  [=I.I=] successfully defined id11@6F.
  [=^.^=] coh id13@7F = (comp13  f1 f2 f3 f4 f5 f6 (_builtin_id  x7) f7 f8 f9 f10 f11 f12) -> (comp11  f1 f2 f3 f4 f5 (_builtin_comp  f6 f7) f8 f9 f10 f11 f12)
  [=I.I=] successfully defined id13@7F.
  [=^.^=] let simpl2 = (comp3  (rew3@2  f1 s2 f4) (id3@2  f1 f4) s1)
  [=I.I=] successfully defined term (!1comp3 (rew3@2 f1 s2 f4) (id3@2 f1 f4) s1) of type (comp3 f1 (builtin_comp2 f2 f3) f4) -> (builtin_id x0).
  [=^.^=] let simpl2- = (comp3  s1- (id3@2-  f1 f4) (rew3@2  f1 s2- f4))
  [=I.I=] successfully defined term (!1comp3 s1- (id3@2- f1 f4) (rew3@2 f1 s2- f4)) of type (builtin_id x0) -> (comp3 f1 (builtin_comp2 f2 f3) f4).
  [=^.^=] let simpl2F = (_builtin_comp  (focus2  f1 f2 f3 f4) (simpl2  s1 s2))
  [=I.I=] successfully defined term (!1builtin_comp2 (focus2 f1 f2 f3 f4) (simpl2 s1 s2)) of type (builtin_comp2 (builtin_comp2 f1 f2) (builtin_comp2 f3 f4)) -> (builtin_id x0).
  [=^.^=] let simpl2F- = (_builtin_comp  (simpl2-  s1- s2-) (focus2-  f1 f2 f3 f4))
  [=I.I=] successfully defined term (!1builtin_comp2 (simpl2- s1- s2-) (focus2- f1 f2 f3 f4)) of type (builtin_id x0) -> (builtin_comp2 (builtin_comp2 f1 f2) (builtin_comp2 f3 f4)).
  [=^.^=] let simpl3 = (comp3  (rew5@3  f1 f2 s3 f5 f6) (id5@3F  f1 f2 f5 f6) (simpl2  s1 s2))
  [=I.I=] successfully defined term (!1comp3 (rew5@3 f1 f2 s3 f5 f6) (id5@3F f1 f2 f5 f6) (simpl2 s1 s2)) of type (comp5 f1 f2 (builtin_comp2 f3 f4) f5 f6) -> (builtin_id x0).
  [=^.^=] let simpl3- = (comp3  (simpl2-  s1- s2-) (id5@3F-  f1 f2 f5 f6) (rew5@3  f1 f2 s3- f5 f6))
  [=I.I=] successfully defined term (!1comp3 (simpl2- s1- s2-) (id5@3F- f1 f2 f5 f6) (rew5@3 f1 f2 s3- f5 f6)) of type (builtin_id x0) -> (comp5 f1 f2 (builtin_comp2 f3 f4) f5 f6).
  [=^.^=] let simpl3F = (_builtin_comp  (focus3  f1 f2 f3 f4 f5 f6) (simpl3  s1 s2 s3))
  [=I.I=] successfully defined term (!1builtin_comp2 (focus3 f1 f2 f3 f4 f5 f6) (simpl3 s1 s2 s3)) of type (builtin_comp2 (comp3 f1 f2 f3) (comp3 f4 f5 f6)) -> (builtin_id x0).
  [=^.^=] let simpl3F- = (_builtin_comp  (simpl3-  s1- s2- s3-) (focus3-  f1 f2 f3 f4 f5 f6))
  [=I.I=] successfully defined term (!1builtin_comp2 (simpl3- s1- s2- s3-) (focus3- f1 f2 f3 f4 f5 f6)) of type (builtin_id x0) -> (builtin_comp2 (comp3 f1 f2 f3) (comp3 f4 f5 f6)).
  [=^.^=] let simpl4 = (comp3  (rew7@4  f1 f2 f3 s4 f6 f7 f8) (id7@4F  f1 f2 f3 f6 f7 f8) (simpl3  s1 s2 s3))
  [=I.I=] successfully defined term (!1comp3 (rew7@4 f1 f2 f3 s4 f6 f7 f8) (id7@4F f1 f2 f3 f6 f7 f8) (simpl3 s1 s2 s3)) of type (comp7 f1 f2 f3 (builtin_comp2 f4 f5) f6 f7 f8) -> (builtin_id x0).
  [=^.^=] let simpl5 = (comp3  (rew9@5  f1 f2 f3 f4 s5 f7 f8 f9 f10) (id9@5F  f1 f2 f3 f4 f7 f8 f9 f10) (simpl4  s1 s2 s3 s4))
  [=I.I=] successfully defined term (!1comp3 (rew9@5 f1 f2 f3 f4 s5 f7 f8 f9 f10) (id9@5F f1 f2 f3 f4 f7 f8 f9 f10) (simpl4 s1 s2 s3 s4)) of type (comp9 f1 f2 f3 f4 (builtin_comp2 f5 f6) f7 f8 f9 f10) -> (builtin_id x0).
  [=^.^=] let simpl5F = (_builtin_comp  (focus5  f1 f2 f3 f4 f5 f6 f7 f8 f9 f10) (simpl5  s1 s2 s3 s4 s5))
  [=I.I=] successfully defined term (!1builtin_comp2 (focus5 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10) (simpl5 s1 s2 s3 s4 s5)) of type (builtin_comp2 (comp5 f1 f2 f3 f4 f5) (comp5 f6 f7 f8 f9 f10)) -> (builtin_id x0).
  [=^.^=] let simpl6 = (comp3  (rew11@6  f1 f2 f3 f4 f5 s6 f8 f9 f10 f11 f12) (id11@6F  f1 f2 f3 f4 f5 f8 f9 f10 f11 f12) (simpl5  s1 s2 s3 s4 s5))
  [=I.I=] successfully defined term (!1comp3 (rew11@6 f1 f2 f3 f4 f5 s6 f8 f9 f10 f11 f12) (id11@6F f1 f2 f3 f4 f5 f8 f9 f10 f11 f12) (simpl5 s1 s2 s3 s4 s5)) of type (comp11 f1 f2 f3 f4 f5 (builtin_comp2 f6 f7) f8 f9 f10 f11 f12) -> (builtin_id x0).
  [=^.^=] let simpl6F = (_builtin_comp  (focus6  f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12) (simpl6  s1 s2 s3 s4 s5 s6))
  [=I.I=] successfully defined term (!1builtin_comp2 (focus6 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12) (simpl6 s1 s2 s3 s4 s5 s6)) of type (builtin_comp2 (comp6 f1 f2 f3 f4 f5 f6) (comp6 f7 f8 f9 f10 f11 f12)) -> (builtin_id x0).
  [=^.^=] let simpl7 = (comp3  (rew13@7  f1 f2 f3 f4 f5 f6 s7 f9 f10 f11 f12 f13 f14) (id13@7F  f1 f2 f3 f4 f5 f6 f9 f10 f11 f12 f13 f14) (simpl6  s1 s2 s3 s4 s5 s6))
  [=I.I=] successfully defined term (!1comp3 (rew13@7 f1 f2 f3 f4 f5 f6 s7 f9 f10 f11 f12 f13 f14) (id13@7F f1 f2 f3 f4 f5 f6 f9 f10 f11 f12 f13 f14) (simpl6 s1 s2 s3 s4 s5 s6)) of type (comp13 f1 f2 f3 f4 f5 f6 (builtin_comp2 f7 f8) f9 f10 f11 f12 f13 f14) -> (builtin_id x0).
  [=^.^=] let simpl7F = (_builtin_comp  (focus7  f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14) (simpl7  s1 s2 s3 s4 s5 s6 s7))
  [=I.I=] successfully defined term (!1builtin_comp2 (focus7 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14) (simpl7 s1 s2 s3 s4 s5 s6 s7)) of type (builtin_comp2 (comp7 f1 f2 f3 f4 f5 f6 f7) (comp7 f8 f9 f10 f11 f12 f13 f14)) -> (builtin_id x0).
  [=^.^=] let simplrew2A = (comp3  (rew2compA  a1 a2 b1 b2) (rrew2A  aU bU) (rew2idA  f1 g1))
  [=I.I=] successfully defined term (!2comp3 (rew2compA a1 a2 b1 b2) (rrew2A aU bU) (rew2idA f1 g1)) of type (!1builtin_comp2 (rew2A a1 b1) (rew2A a2 b2)) -> (!1builtin_id (builtin_comp2 f1 g1)).
  [=^.^=] let simplrew3 = (comp3  (rew3comp@2  f1 a b f3) (rrew3@2  f1 abU f3) (rew3id@2  f1 f2 f3))
  [=I.I=] successfully defined term (!2comp3 (rew3comp@2 f1 a b f3) (rrew3@2 f1 abU f3) (rew3id@2 f1 f2 f3)) of type (!1builtin_comp2 (rew3@2 f1 a f3) (rew3@2 f1 b f3)) -> (!1builtin_id (comp3 f1 f2 f3)).
  [=^.^=] let simplrew3-@2 = (comp3  (rew3id@2-  f1 f2 f3) (rrew3@2  f1 abU- f3) (rew3comp@2-  f1 a b f3))
  [=I.I=] successfully defined term (!2comp3 (rew3id@2- f1 f2 f3) (rrew3@2 f1 abU- f3) (rew3comp@2- f1 a b f3)) of type (!1builtin_id (comp3 f1 f2 f3)) -> (!1builtin_comp2 (rew3@2 f1 a f3) (rew3@2 f1 b f3)).
  [=^.^=] let simplrew3A = (comp3  (rew3compA  a1 a2 b1 b2 c1 c2) (rrew3A  aU bU cU) (rew3idA  f1 f2 f3))
  [=I.I=] successfully defined term (!2comp3 (rew3compA a1 a2 b1 b2 c1 c2) (rrew3A aU bU cU) (rew3idA f1 f2 f3)) of type (!1builtin_comp2 (rew3A a1 b1 c1) (rew3A a2 b2 c2)) -> (!1builtin_id (comp3 f1 f2 f3)).
  [=^.^=] let simplrew5 = (comp3  (rew5comp@3  f1 f2 a b f4 f5) (rrew5@3  f1 f2 abU f4 f5) (rew5id@3  f1 f2 f3 f4 f5))
  [=I.I=] successfully defined term (!2comp3 (rew5comp@3 f1 f2 a b f4 f5) (rrew5@3 f1 f2 abU f4 f5) (rew5id@3 f1 f2 f3 f4 f5)) of type (!1builtin_comp2 (rew5@3 f1 f2 a f4 f5) (rew5@3 f1 f2 b f4 f5)) -> (!1builtin_id (comp5 f1 f2 f3 f4 f5)).
  [=^.^=] let simplrew7 = (comp3  (rew7comp@4  f1 f2 f3 a b f5 f6 f7) (rrew7@4  f1 f2 f3 abU f5 f6 f7) (rew7id@4  f1 f2 f3 f4 f5 f6 f7))
  [=I.I=] successfully defined term (!2comp3 (rew7comp@4 f1 f2 f3 a b f5 f6 f7) (rrew7@4 f1 f2 f3 abU f5 f6 f7) (rew7id@4 f1 f2 f3 f4 f5 f6 f7)) of type (!1builtin_comp2 (rew7@4 f1 f2 f3 a f5 f6 f7) (rew7@4 f1 f2 f3 b f5 f6 f7)) -> (!1builtin_id (comp7 f1 f2 f3 f4 f5 f6 f7)).
  [=^.^=] let simplrrew = (comp3  (rrew2compA  s1 s2 r1 r2) (rrrew2A  sU rU) (rrew2idA  a1 b1))
  [=I.I=] successfully defined term (!3comp3 (rrew2compA s1 s2 r1 r2) (rrrew2A sU rU) (rrew2idA a1 b1)) of type (!2builtin_comp2 (rrew2A s1 r1) (rrew2A s2 r2)) -> (!2builtin_id (rew2A a1 b1)).
  [=^.^=] let red3 = (_builtin_comp  (rew5@3  f1 f2 s f5 f6) (id5@3F  f1 f2 f5 f6))
  [=I.I=] successfully defined term (!1builtin_comp2 (rew5@3 f1 f2 s f5 f6) (id5@3F f1 f2 f5 f6)) of type (comp5 f1 f2 (builtin_comp2 f3 f4) f5 f6) -> (comp3 f1 (builtin_comp2 f2 f5) f6).
  [=^.^=] let red3- = (_builtin_comp  (id5@3F-  f1 f2 f5 f6) (rew5@3  f1 f2 s f5 f6))
  [=I.I=] successfully defined term (!1builtin_comp2 (id5@3F- f1 f2 f5 f6) (rew5@3 f1 f2 s f5 f6)) of type (comp3 f1 (builtin_comp2 f2 f5) f6) -> (comp5 f1 f2 (builtin_comp2 f3 f4) f5 f6).
  [=^.^=] let red3F = (_builtin_comp  (focus3  f1 f2 f3 f4 f5 f6) (red3  f1 f2 s f5 f6))
  [=I.I=] successfully defined term (!1builtin_comp2 (focus3 f1 f2 f3 f4 f5 f6) (red3 f1 f2 s f5 f6)) of type (builtin_comp2 (comp3 f1 f2 f3) (comp3 f4 f5 f6)) -> (comp3 f1 (builtin_comp2 f2 f5) f6).
  [=^.^=] let red3F- = (_builtin_comp  (red3-  f1 f2 s f5 f6) (focus3-  f1 f2 f3 f4 f5 f6))
  [=I.I=] successfully defined term (!1builtin_comp2 (red3- f1 f2 s f5 f6) (focus3- f1 f2 f3 f4 f5 f6)) of type (comp3 f1 (builtin_comp2 f2 f5) f6) -> (builtin_comp2 (comp3 f1 f2 f3) (comp3 f4 f5 f6)).
  [=^.^=] let red3U = (simpl2F  (simplrew5  f1 f2 f5 f6 sU) (id5@3FU  f1 f2 f5 f6))
  [=I.I=] successfully defined term (!1simpl2F (simplrew5 f1 f2 f5 f6 sU) (id5@3FU f1 f2 f5 f6)) of type (!1builtin_comp2 (!1builtin_comp2 (rew5@3 f1 f2 s1 f5 f6) (id5@3F f1 f2 f5 f6)) (!1builtin_comp2 (id5@3F- f1 f2 f5 f6) (rew5@3 f1 f2 s2 f5 f6))) -> (!1builtin_id (comp5 f1 f2 (builtin_comp2 f3 f4) f5 f6)).
  [=^.^=] let red3FU = (simpl2F  (focus3U  f1 f2 f3 f4 f5 f6) (red3U  f1 f2 sU f5 f6))
  [=I.I=] successfully defined term (!1simpl2F (focus3U f1 f2 f3 f4 f5 f6) (red3U f1 f2 sU f5 f6)) of type (!1builtin_comp2 (!1builtin_comp2 (focus3 f1 f2 f3 f4 f5 f6) (!1builtin_comp2 (rew5@3 f1 f2 s1 f5 f6) (id5@3F f1 f2 f5 f6))) (!1builtin_comp2 (!1builtin_comp2 (id5@3F- f1 f2 f5 f6) (rew5@3 f1 f2 s2 f5 f6)) (focus3- f1 f2 f3 f4 f5 f6))) -> (!1builtin_id (builtin_comp2 (comp3 f1 f2 f3) (comp3 f4 f5 f6))).
  [=^.^=] let red3CU = (simpl2F  (id5@3FCU  f1 f2 f5 f6) (simplrew5  f1 f2 f5 f6 sU))
  [=I.I=] successfully defined term (!1simpl2F (id5@3FCU f1 f2 f5 f6) (simplrew5 f1 f2 f5 f6 sU)) of type (!1builtin_comp2 (!1builtin_comp2 (id5@3F- f1 f2 f5 f6) (rew5@3 f1 f2 s1 f5 f6)) (!1builtin_comp2 (rew5@3 f1 f2 s2 f5 f6) (id5@3F f1 f2 f5 f6))) -> (!1builtin_id (comp3 f1 (builtin_comp2 f2 f5) f6)).
  [=^.^=] let red3FCU = (simpl2F  (red3CU  f1 f2 sU f5 f6) (focus3CU  f1 f2 f3 f4 f5 f6))
  [=I.I=] successfully defined term (!1simpl2F (red3CU f1 f2 sU f5 f6) (focus3CU f1 f2 f3 f4 f5 f6)) of type (!1builtin_comp2 (!1builtin_comp2 (!1builtin_comp2 (id5@3F- f1 f2 f5 f6) (rew5@3 f1 f2 s1 f5 f6)) (focus3- f1 f2 f3 f4 f5 f6)) (!1builtin_comp2 (focus3 f1 f2 f3 f4 f5 f6) (!1builtin_comp2 (rew5@3 f1 f2 s2 f5 f6) (id5@3F f1 f2 f5 f6)))) -> (!1builtin_id (comp3 f1 (builtin_comp2 f2 f5) f6)).
  [=^.^=] let rew2@2id@1R = (comp3  (id2@1-  f) (rew2@2  (_builtin_id  x) a) (id2@1  g))
  [=I.I=] successfully defined term (!1comp3 (id2@1- f) (rew2@2 (builtin_id x) a) (id2@1 g)) of type f -> g.
  [=^.^=] coh rew2@2id@1 = (rew2@2id@1R  a) -> a
  [=I.I=] successfully defined rew2@2id@1.
  [=^.^=] coh rew2@2id@1- = a -> (rew2@2id@1R  a)
  [=I.I=] successfully defined rew2@2id@1-.
  [=^.^=] coh rew@2id@1U = (_builtin_comp  (rew2@2id@1  a) (rew2@2id@1-  a)) -> (_builtin_id  (rew2@2id@1R  a))
  [=I.I=] successfully defined rew@2id@1U.
  [=^.^=] coh rew2id@1CU = (_builtin_comp  (rew2@2id@1-  a) (rew2@2id@1  a)) -> (_builtin_id  a)
  [=I.I=] successfully defined rew2id@1CU.
  [=^.^=] let rew2@1id@2R = (comp3  (id2@2-  f) (rew2@1  a (_builtin_id  y)) (id2@2  g))
  [=I.I=] successfully defined term (!1comp3 (id2@2- f) (rew2@1 a (builtin_id y)) (id2@2 g)) of type f -> g.
  [=^.^=] coh rew2@1id@2 = (rew2@1id@2R  a) -> a
  [=I.I=] successfully defined rew2@1id@2.
  [=^.^=] coh rew2@1id@2- = a -> (rew2@1id@2R  a)
  [=I.I=] successfully defined rew2@1id@2-.
  [=^.^=] coh rew2@1id@2U = (_builtin_comp  (rew2@1id@2  a) (rew2@1id@2-  a)) -> (_builtin_id  (rew2@1id@2R  a))
  [=I.I=] successfully defined rew2@1id@2U.
  [=^.^=] coh rew2@1id@2CU = (_builtin_comp  (rew2@1id@2-  a) (rew2@1id@2  a)) -> (_builtin_id  a)
  [=I.I=] successfully defined rew2@1id@2CU.
  [=^.^=] coh exch = (_builtin_comp  (rew2@1  a h) (rew2@2  g b)) -> (_builtin_comp  (rew2@2  f b) (rew2@1  a k))
  [=I.I=] successfully defined exch.
  [=^.^=] coh exch- = (_builtin_comp  (rew2@2  f b) (rew2@1  a k)) -> (_builtin_comp  (rew2@1  a h) (rew2@2  g b))
  [=I.I=] successfully defined exch-.
  [=^.^=] coh exchU = (_builtin_comp  (exch  a b) (exch-  a b)) -> (_builtin_id  (_builtin_comp  (rew2@1  a h) (rew2@2  g b)))
  [=I.I=] successfully defined exchU.
  [=^.^=] let eh = (comp5  (rew2A  (rew2@1id@2-  a) (rew2@2id@1-  b)) (red3F  (id2@2-  (_builtin_id  x)) (rew2@1  a (_builtin_id  x)) (id2@2@1U  x) (rew2@2  (_builtin_id  x) b) (id2@1  (_builtin_id  x))) (rew3A  (id2@/1-/2-/-  x) (exch  a b) (id2@/1/2/  x)) (red3F-  (id2@1-  (_builtin_id  x)) (rew2@2  (_builtin_id  x) b) (id2@1@2U-  x) (rew2@1  a (_builtin_id  x)) (id2@2  (_builtin_id  x))) (rew2A  (rew2@2id@1  b) (rew2@1id@2  a)))
  [=I.I=] successfully defined term (!2comp5 (!1rew2A (rew2@1id@2- a) (rew2@2id@1- b)) (!1red3F (id2@2- (builtin_id x)) (rew2@1 a (builtin_id x)) (id2@2@1U x) (rew2@2 (builtin_id x) b) (id2@1 (builtin_id x))) (!1rew3A (id2@/1-/2-/- x) (exch a b) (id2@/1/2/ x)) (!1red3F- (id2@1- (builtin_id x)) (rew2@2 (builtin_id x) b) (id2@1@2U- x) (rew2@1 a (builtin_id x)) (id2@2 (builtin_id x))) (!1rew2A (rew2@2id@1 b) (rew2@1id@2 a))) of type (!1builtin_comp2 a b) -> (!1builtin_comp2 b a).

  $ catt coverage/eckmann-hilton-optimized.catt
  [=^.^=] coh unitl = (_builtin_comp  (_builtin_id  _) f) -> f
  [=I.I=] successfully defined unitl.
  [=^.^=] coh unit = (_builtin_comp  (_builtin_id  x) (_builtin_id  x)) -> (_builtin_id  x)
  [=I.I=] successfully defined unit.
  [=^.^=] coh lsimp = (unitl  (_builtin_id  x)) -> (unit  x)
  [=I.I=] successfully defined lsimp.
  [=^.^=] coh Ilsimp = I((unitl  (_builtin_id  x))) -> I((unit  x))
  [=I.I=] successfully defined Ilsimp.
  [=^.^=] coh exch = (_builtin_comp  (_builtin_comp  _ [b]) (_builtin_id  (_builtin_comp  f k)) (_builtin_comp  [a] _)) -> (_builtin_comp  [a] [b])
  [=I.I=] successfully defined exch.
  [=^.^=] coh eh1 = (_builtin_comp  a b) -> (_builtin_comp  I((unitl  f)) (_builtin_comp  (_builtin_comp  _ [a]) (_builtin_comp  (unitl  g) I(op_{1}((unitl  g)))) (_builtin_comp  [b] _)) op_{1}((unitl  h)))
  [=I.I=] successfully defined eh1.
  [=^.^=] let eh2 = (_builtin_comp  [(Ilsimp  _)] [(_builtin_comp  (_builtin_comp  _ [(_builtin_comp  (_builtin_comp  [(lsimp  _)] [op_{1}((Ilsimp  _))]) U((unit  _)))] _) (exch  b a))] [op_{1}((lsimp  _))])
  [=I.I=] successfully defined term (!1builtin_comp3 [(Ilsimp x)] [(!2builtin_comp2 (!1builtin_comp3 (builtin_comp2 (builtin_id x) [a]) [(!2builtin_comp2 (!1builtin_comp2 [(lsimp x)] [(Ilsimp_op{1} x)]) (unit_Unit x))] (builtin_comp2 [b] (builtin_id x))) (exch b a))] [(lsimp_op{1} x)]) of type (!1builtin_comp3 (unitl^-1 (builtin_id x)) (!1builtin_comp3 (builtin_comp2 (builtin_id x) [a]) (!1builtin_comp2 (unitl (builtin_id x)) (unitl_op{1}^-1 (builtin_id_op{1} x))) (builtin_comp2 [b] (builtin_id x))) (unitl_op{1} (builtin_id_op{1} x))) -> (!1builtin_comp3 (unit^-1 x) (builtin_comp2 [b] [a]) (unit_op{1} x)).
  [=^.^=] let eh = (_builtin_comp  (eh1  a b) (eh2  a b) I(op_{1}((eh2  b a))) I(op_{1}((eh1  b a))))
  [=I.I=] successfully defined term (!2builtin_comp4 (eh1 a b) (eh2 a b) (!1builtin_comp3 [(Ilsimp_op{1}^-1 x)] [(!2builtin_comp2 (exch_op{1}^-1 b a) (!1builtin_comp3 (builtin_comp2_func[1]_op{1} (builtin_id_op{1} x) b) [(!2builtin_comp2 (unit_Unit_op{1}^-1 x) (!1builtin_comp2 [(lsimp_op{1}^-1 x)] [(Ilsimp_op{1}_op{1}^-1 x)]))] (builtin_comp2_func[1]_op{1} a (builtin_id_op{1} x))))] [(lsimp_op{1}_op{1}^-1 x)]) (eh1_op{1}^-1 b a)) of type (!1builtin_comp2 a b) -> (!1builtin_comp2_op{1} b a).
