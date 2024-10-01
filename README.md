# Catt - An infinity categorical coherence typechecker

Catt is an implementation of a type system checking coherences in [Grothendieck-Maltsiotis ω-categories](https://arxiv.org/abs/1009.2331). The underlying type theoretical translation is described by [Finster-Mimram](https://arxiv.org/abs/1706.02866).

This is my personnal implementation of this theory. For a more complete implementation, which also accounts for different flavours of semi-strict ω-categories, check out [catt.io](https://github.com/ericfinster/catt.io). Older, and more experimental implementation that should be mentioned for the sake of completeness, but are now superseeded are [Samuel Mimram's OCaml version](https://github.com/smimram/catt), and [Eric Finster's Haskell version](https://github.com/ericfinster/catt).

There is an [online version](https://thibautbenjamin.github.io/catt/) of this implementation.

## Installation

### Installing from opam

Incoming...

### Installing from source with opam
Make sure `opam` is installed, clone the project and move to the directory where you cloned it, then run the following to install catt:
```
opam install ./catt.opam
```
The Coq plugin can be installed with the following command
```
opam install ./coq-catt-plugin.opam
```

### Building from source with dune and opam
Make sure `opam` is installed, clone the project and move to the directory where you cloned it.

To build `catt` locally, run the following commands:
```
opam install --deps-only ./catt.opam
dune build catt.install
```

To build the Coq plugin, run the following commands:
```
opam install --deps-only ./coq-catt-plugin.opam
dune build coq-catt-plugin.install
```

### Using nix

This repository contains a `flake.nix` file that defines the packages `catt` and `coq-catt-plugin`, as well as `catt-mode`, an editing mode for catt in emacs.

## Syntax
There are two keywords to define a new operation:

* Firstly, the `coh` keyword, used as follows:
	```
	coh name ps : ty
	```
	defines a primitive coherence with arguments `ps` forming a pasting scheme and return type `ty`.

* Secondly, the `let` keyword, used as follows:
	```
	let name args : ty = tm
	let name args = tm
	```
	declares an operation with arguments `args` and whose definition is `tm`. The type `ty` can be specified to be checked or left implicit.

### Examples
`catt` is a theory of unbiased ω-categories, which means that one can declare composites of any arity. For instance, the binary and ternary composites can be defined as follows:
```
coh binarycomp (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) : x -> z
coh ternarycomp (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) (w : *) (h : z -> w) : x -> w
```
Similarly, the identity cell can be defined as follows:
```
coh identity (x : *) : x -> x
```
Higher-dimensional cells witnessing weak laws involving the composites and the identities cells, such as unitors and associators, can then be defined as follows:
```
coh unit (x : *) (y : *) (f : x -> y) : binarycomp f (identity y) -> f
coh assoc (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) (w : *) (h : z -> w) : binarycomp (binarycomp f g) h -> binarycomp f (binarycomp g h)
```
More composition operations exist for higher-dimensional cells: for instance for 2-cells we can define the vertical composition, the horizontal compositions and the left and right whiskerings:
```
coh vert (x : *) (y : *) (f : x -> y) (g : x -> y) (h : x -> y) (a : f -> g) (b : g -> h) : f -> h
coh horiz (x : *) (y : *) (f : x -> y) (g : x -> y) (a : f -> g) (z : *) (h : y -> z) (k : y -> z) (b : h -> k) : binarycomp f h -> binarycomp g k
coh whiskl (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) (h : y -> z) (a : g -> h) : binarycomp f g -> binarycomp f h
coh whiskr (x : *) (y : *) (f : x -> y) (g : x -> z) (a : f -> g) (z : *) (h : y -> z) : binarycomp f h -> binarycomp g h
```

These coherences can be combined together to define terms in arbitrary contexts. For instance, the square of an endomorphism can be defined using the binary composite as follows:
```
let sq (x : *) (f : x -> x) : x -> x = binarycomp f f
```
while the following defines a biased ternary composite built from combining binary composites:
```
let ternarycomp (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) (w : *) (h : z -> w) : x -> w = binarycomp (binarycomp f g)
```

## Additional features

### Changing settings
There are a few settings that control the exact behaviour of `catt`. These settings can be set and unset at any point during typechecking using the command:
```
set [SETTING] = [VALUE]
```
The simplest setting is `verbosity`, which can be set to a number from `0` to `5`. Boolean settings are set using the values `t` for true and `f` for false.

### Implicit arguments
Some arguments to be specified for each operation can always be inferred, and by default these are left implicit. Specifically, all arguments that already appear in the type of another argument, are by default implicit. This can be turned off at any point with the following instruction:
```
set explicit_substitutions = t
```
For instance, the unitor using explicit arguments can be defined as follows:
```
set explicit_substitutions = t
coh unit_explicit (x : *) (y : *) (f : x -> y) : binarycomp x y f y (id y) -> f
set explicit_substitutions = f
```
### Wildcards
Sometimes, more arguments can be inferred, and these may be replaced by the wildcard symbol `_`. For instance, the unitor can be defined as follows:
```
coh unit_wild (x : *) (y : *) (f : x -> y) : binarycomp f (identity _) -> f
```

### Reduced syntax for coherence
This feature has been taken from [catt.io](https://github.com/ericfinster/catt.io). One can exploit the fact that pasting schemes are equivalent to well-parenthesised expressions to give a more concise syntax for them. For instance, one, can define the composition of two 1-cells as follows:
```
coh binarycomp (x(f)y(g)z) : x -> z
```
Internally, these parenthesised expressions are reduced to contexts and are treated the same way.

### Built-in compositions and identities
Some useful coherences are built-in. This allows for two things: first, it is not necessary as a user to define those coherences that already exist, and, secondly, it allows to have an internal hardcoded mechanism to manage coherence schemes instead of single coherences. The built-ins can be deactivated via the command-line as follows `catt --no-builtins [FILE]` or `dune exec -- catt --no-builtin [FILE]`. When built-ins are activated, the user is prevented from defining terms or operations that have the same name as a built-in.

#### Identity
The identity coherence previously defined is also saved as a built-in under the name `id`. Thus one can always just use `id` without the need to define it first.

#### Compositions
The variadic composition of 1-cells is also defined as built-in, and named `comp`. The name `comp` is thus more than a single coherence but a family of coherences. When applied to n arguments, it produces the n-ary composite. In practice this means that one can write
```
coh unbias (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) (w : *) (h : z -> w) : comp (comp f g) h -> comp f g h
```
where here the same name `comp` is used for the binary composition and the ternary one.


#### Example
The unitor defined above can be defined directly using the the built-ins, not requiring to introduce coherences for the composition and identity before
```
coh unit (x) : comp f (id _) -> f
```

### Suspension
Every definition can be automatically raised to a higher dimension by suspension. Formally this amounts to replacing the type of object `*` with an arrow type. For instance, the identity coherence on 1-cells can be defined as the suspension of the identity coherence on 0-cells. We provide a way to express this, by using the `!` in front of the name to indicate that it should be suspended. The following two definitions define the same term, representing the identity on 1-cells
```
coh identity1cells (x(f)y) : f -> f
let identity1cells (x : *) (y : *) (f : x -> y) : f -> f = !id f
```
By default, the suspensions can be left implicit and the system will automatically insert the suspension at the right places. For instance, one can define the vertical composition of 2-cells, which is the suspension of the composition of 0-cells as follows
```
let vertical_comp (x : *) (y : *) (f : x -> y) (g : x -> y) (a : f -> g) (h : x -> y) (b : g -> h)
                  : f -> h = comp a b
```
The implicit use of suspensions can be deactivated with
```
set implicit_suspension = f
```

Semantically, taking the suspension of a term representing an operation of ω-categories amounts to considering the same operation for the ω-categorical structure of the hom-globular set. A complete account of the construction of the suspension and semantical interpretation is given in [this article](https://arxiv.org/abs/2402.01611).

### Opposites
The language of `catt` is invariant under the operation of formally reversing all the directions of the cells in a given dimension. We call this operation an opposite, and it is provided by the following syntax
```
op { [NUMBER] } (TERM)
```
where the number indicates in which direction one is taking the opposite. For instance, consider the folloiwng example:
```
let opwhiskl (x : *) (y : *) (z : *) (f : x -> y) (f' : x -> y) (a : f -> f') (g : y -> z)
    = op { 1 } (whiskl g a)
```
`whiskl g a` is not well defined in the given context since that would require the target of `g` to be the source of the source of `a` which is not the case. However, taking the 1-opposite formally reverses the direction of the 1-cells, and this typing condition then requires the target of the target of `a` to be the source of `g`, which is the case in the given context (both are `y`). So this definition is valid. The 1-opposite of the right whiskering is the left whiskering and in the above example the term `op { 1 } (whiskl g a)` actually computes to `whiskr a g`.

Semantically, taking the opposite of a term representing an operation of ω-categories amounts to considering the same operation for the ω-categorical structure of the opposite globular set. An account of the algorithm used to compute the opposite and its semantical interpretation is given in [this article](https://arxiv.org/abs/2402.01611).

### Inverses and invertibility witnesses
Some terms, like the associators or identities, happen to be weakly invertible. It is actually syntactically easy to decide whether a term is invertible. If a term only contains variables of dimension lower than itself, then it is invertible. Otherwise it contains at least one variable of the same dimension as itself and thus is not invertible. `catt` can automatically compute a chosen inverse for those terms which are invertible, as well as a cancellation witness (i.e., a cell going from the composite of the cell with its chosen inverse to an identity). A complete account of the algorithms we use to compute the chosen inverses and cancellation witnesses can be found in [this article](https://arxiv.org/abs/2406.12127).

#### Inverses
Computing a chosen inverse of an invertible term can be done by the following syntax:
```
I [TERM]
```
For instance the associator and its chosen inverse of the associator can be given as follows:
```
coh assoc (x(f)y(g)z(h)w) :  comp (comp f g) h -> comp f (comp g h)
let assoc- (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) (w : *) (h : z -> w) : comp f (comp g h) -> comp (comp f g) h = I (assoc f g h)
```
In this case, the chosen inverse is the associator going the opposite direction. There are more complex cases, where one has, for instance, a composite of associators. In this case, the chosen inverse will be a composite of the inverse associators in the opposite order.

#### Invertibility witness
Not only can `catt` compute some chosen inverses, but it can also compute any part of the coinductively defined data that makes up the invertibility. This is done by computing cancellation witnesses, which are given by the syntax
```
U [TERM]
```
Given a term `t` of type `u -> v`, the cancellation witness `U t` is a cell of type `comp t (I t) -> id (u)`. For instance, here is the cancellation witness for the associator and its inverse:
```
let assocU (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) (w : *) (h : z -> w) : comp (assoc f g h) (assoc- f g h) -> id (comp (comp f g) h)
```
In this case, the cancellation witness is a single coherence, but more complex cases are possible, like for the case of a composite of associators, where the cancellation witness successively uses the cancellation witnesses of the associators and reassociates the whole term.

All the rest of the inveritbility data can be obtained by combining `U` and `I` and iterating `U`. Indeed, the procedure computing `U t` always produce a term that is itself invertible, so on which one can call `I` and `U`. Moreover, one can get the other cancellation witness of type `comp (I t) t -> id v` as `U (I t)` since `I` is involutive.

### Functoriality of coherences and terms
All the coherences that one can define are functorial in their codimension-0 arguments, and this fact is also part of the implementation. The argument with respect to which the functoriality is applied is specified between square brackets. For instance the right whiskering can be seen as the functoriality of the composition with respect to its first argument, which can be thought of as making the cell `a` act in the context of `comp f g` to change it into `comp f' g`.
```
let whiskr (x : *) (y : *) (f : x -> y) (f' : x -> y) (a : f -> f')
                   (z : *) (g : y -> z)
	   : comp f g -> comp f' g = comp [a] g
```
One can also use fuctoriality with respect to multiple variables at the same time. For instance, the horizontal composition of two 2-cells is the functoriality of the composition with respect to both its arguments.
```
let horiz (x : *) (y : *) (f : x -> y) (f' : x -> y) (a : f -> f')
                  (z : *) (g : y -> z) (g' : y -> z) (b : g -> g')
 	  : comp f g -> comp f' g' = comp [a] [b]
```
The functorialisation also works recursively for terms. Given any term and a variable in that term of the same dimension than the term, catt can compute the functorialisation of the term with respect to this argument, which is again specified syntactically by square brackets in the applciation.

This is partially described in [this thesis](https://hal.science/tel-03106197), a more complete account is in preparation.

### naturality of the coherences and terms
Given a coherence or a term and an upwards closed subset of variables of codimension 1 in it, `catt` can compute the witness of naturality of this term with respect to that set of variables. This is again indicated with square bracket around the corresponding arguments of the applciation. In order to mark implicit arguements, we provide the construct `@`, which when given before a name indicates that the substitution in this case is explicit. This for instance lets us define the square composite as follows:
```
let sqcomp (x : *) (y : *) (z : *) (x' : *) (y' : *) (z ' : *)
           (f : x -> y) (g : y -> z) (f' : x' -> y') (g' : y' -> z')
           (xx : x -> x') (yy : y -> y') (zz : z -> z')
           (a : comp f yy -> comp xx f') (b : comp g zz -> comp yy g')
           : comp (comp f g) zz -> comp xx (comp f' g')
           = @comp [_] [_] [a] [_] [b]
```
It also lets us define the composite of a square with a triangle as follows:
```
let trcomp (x : *) (y : *) (z : *) (y' : *) (z ' : *)
           (f : x -> y) (g : y -> z) (f' : x -> y') (g' : y' -> z')
           (yy : y -> y') (zz : z -> z')
           (a : comp f yy -> f') (b : comp g zz -> comp yy g')
           : comp (comp f g) zz -> comp f' g'
           = @comp _ [_] [a] [_] [b]
```
A formal account of this principle is in preparation.

## Practical use
### The --debug flag
Calling `catt --debug [FILE]` will make it so that if there is an error in the file, the program will not abort, but show a menu where the user can either abort the program, ignore the error and keep checking the file, or drop in an interactive mode. For the last option, the environment of the interactive is that at the point of failure, so any coherence defined in the file causing the failure before that point is directly accessible and usable.

### The --no-builtins flag
Calling `catt --no-builtin [FILE]` will deactivate the use of the built-in identities and composition, allowing the user to define their own coherences or terms named `id` and `comp`.

### The --keep-going flag
Calling `catt --keep-going [FILE]` will make it so that `catt` will report errors but will keep running on the file and exit with a success even if the file does not typecheck properly. This is not the default behaviour, as in a typical use case, later definitions depend on earlier ones, so if a defined coherence or term is invalid, all further coherences and terms depending on it also fail. This option is useful for scripting and testing.


## Coq plugin
`catt` also provide a plugin for the proof assistant `coq` (packaged separately, called `coq-catt-plugin`), that allows one to export any defined term in `catt` into a function computing higher identity witnesses in `coq`. Once the plugin is installed, write the following to load it at the head of a `coq` file:
```
From Catt Require Import Loader.
```
You can then use the `Catt` command in `coq` as follows:
```
Catt [NAMES] FROM FILE [PATH].
```
where `[NAMES]` is a list of names of `catt` terms and `[PATH]` is a file containing the definition of those `catt` terms. Upon evaluation of this line, `coq` will call `catt` on the given file and export the listed terms into `coq` terms, whose names will be given as `catt_[NAME]`. For instance, one can write the following:
```
Catt "whiskr" From File "../example/file.catt".

Print catt_whiskr.
```
