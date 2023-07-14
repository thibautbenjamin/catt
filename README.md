# Catt - An infinity categorical coherence typechecker

Catt is an implementation of a type system checking coherences in [Grothendieck-Maltsiotis infinity categories](https://arxiv.org/abs/1009.2331). The underlying type theoretical translation is described by [Finster-Mimram](https://arxiv.org/abs/1706.02866).

This is my personnal implementation of this theory. For a more complete implementation, which also accounts for different flavours of semi-strict omegaècategories, check out [catt.io](https://github.com/ericfinster/catt.io). Older, and more experimental implementation that should be mentioned for the sake of completeness, but are now superseeded are [Samuel Mimram's OCaml version](https://github.com/smimram/catt), and [Eric Finster's Haskell version](https://github.com/ericfinster/catt).

There is an [online version](https://thibautbenjamin.github.io/catt/) of this implementation

## Syntax
There are two keywords to define a new operation  
```
coh name ps : ty
```
to define a primitive coherence with arguments ps forming a pasting scheme and return type ty
```
let name args : ty = tm  
let name args = tm
```
to declare an operation with arguments args and whose definition is tm, the type ty can be specified to be checked or left implicit.

## Additional features

### Implicit arguments
The arguments to be specified for each operation can be inferred, thus the system will always choose for you some arguments to be implicit. The chosen implicit arguments are the ones that appear explicitly in the type of further arguments. Specifically, all the arguments of definitions that appear in the types of other arguments are considered implicit by default. This can be turned off at any point with the following instruction
```
set explicit_substitutions = t
```
For instance, defining the identity, composition and unitor can be done as follows
```
coh id (x : *) : x -> x
coh comp (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) : x -> z
coh unit (x : *) (y : *) (f : x -> y) : comp f (id y) -> f

set explicit_substitutions = t
coh unit_explicit (x : *) (y : *) (f : x -> y) : comp x y f y (id y) -> f
```
### Wildcards
Implicit arguments that can be inferred my be replaced by wildcards. For instance, the unitor can also be defined as
For instance, defining the identity, composition and unitor can be done as follows
```
set explicit_substitutions = f
coh unit_wild (x : *) (y : *) (f : x -> y) : comp f (id _) -> f
```

### Reduced syntax for coherence
This feature has been taken from [catt.io](https://github.com/ericfinster/catt.io). One can exploit the fact that pasting schemes are equivalent to well-parenthesised expressions to give a more concise syntax for them. For instance, one, can define the composition of two 1-cells as follows
```
coh comp (x(f)y(g)z) : x -> z
```
Internally, this reduces to contexts and are treated the same way

### Suspension
Every definition can be automatically raised to a higher dimension by suspension. Formally this amounts to replacing the type of object `*` with an arrow type. For instance, the identity coherence on 1-cells can be defined as the suspension of the identity coherence on 0-cells. We provide a way to express this, by using the `!` in front of the name to indicate that it should be suspended. Thus, the identity on 1-cells can be defined as
```
let id1 (x : *) (y : *) (f : x -> y) : f -> f = !id f
```
By default, the suspensions can be left implicit and the system will automatically insert the suspension at the right places. For instance, one can define the vertical composition of 2-cells, which is the suspension of the composition of 0-cells as follows
```
let vertical_comp (x : *) (y : *) (f : x -> y) (g : x -> y) (a : f -> g) (h : x -> y) (b : g -> h) : f -> h : comp a b 
```
The implicit use of suspensions can be deactivated with
```
set implicit_suspension = f
```

### Functoriality of operations
All the operations that one could define are functorial, and this fact is also part of the implementation. The argument with respect to which the functoriality is applied is specified between square brackets. For instance the right whiskering can be seen as the functoriality of the composition with respect to its first argument. 
```
let rewrite-in-comp (x : *) (y : *) (f : x -> y) (f' : x -> y) (a : f -> f')
                            (z : *) (g : y -> z)
	            : comp f g -> comp f' g = comp [a] g
```
One can also use fuctoriality with respect to multiple variables at the same time. For instance, the horizontal composition of two 2-cells is the functoriality of the composition with respect to both its arguments.
```
let rewrite-in-comp-both (x : *) (y : *) (f : x -> y) (f' : x -> y) (a : f -> f')
                                 (z : *) (g : y -> z) (g' : y -> z) (b : g -> g')
 	            : comp f g -> comp f' g' = comp [a] [b]
```
