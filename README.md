# Catt - An infinity categorical coherence typechecker

Catt is an implementation of a type system checking coherences in [Grothendieck-Maltsiotis infinity categories](https://arxiv.org/abs/1009.2331). The underlying type theoretical translation is described by [Finster-Mimram](https://arxiv.org/abs/1706.02866).

The implementation is written in OCaml and is based of [Samuel Mimram's implementation](https://github.com/smimram/catt), with additional features and corrections. There is also an [Haskell implementation by Eric Finster](https://github.com/ericfinster/catt)

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
The arguments to be specified for each operation can be inferred, thus the system will always choose for you some arguments to be implicit. The chosen implicit arguments are the ones that appear explicitly in the type of further arguments. 

### Suspension
One can always transfer a definition from a lower dimension to a higher dimension, and this is featured in this implementation. For instance one can define the identity coherence on 0-cells
```
coh id (x : *) : x
```
and then apply it freely to higher dimensional cells
```
let id1 (x : *) (y : *) (f : x -> y) : f -> f = id f
```

### Functoriality of operations
All the operations that are defined in the system are functorial, and this fact is also automated. The argument with respect to which the functoriality is applied is specified between square brackets. For instance if one defines the composition  
```
coh comp (x : *) (y : *) (f : x -> y) (z : *) (g : y -> z) : x -> z  
```
then applying functoriality with respect to the first variable would look like   
```
let rewrite-in-comp (x : *) (y : *) (f : x -> y) (f' : x -> y) (a : f -> f')
                            (z : *) (g : y -> z)
	            : comp f g -> comp f' g = comp [a] g
```