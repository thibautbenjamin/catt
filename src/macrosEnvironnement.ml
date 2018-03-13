open Var
open Kernel
open Common
       
let mEnv : ((Var.t * (tm list -> tm)) list) ref = ref []

