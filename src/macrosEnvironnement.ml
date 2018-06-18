open Kernel
open Common
       
let mEnv : ((Var.t * (ctx * (tm list) -> tm)) list) ref = ref []

