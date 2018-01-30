open ExtSyntax
open Common
       
let mEnv : ((var * (expr list -> expr)) list) ref = ref []

