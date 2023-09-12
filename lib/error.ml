exception UnknownId of string
exception NotEqual of string * string
exception DoubledVar of string
exception DoubleDef of string
exception UnknownOption of string
exception NotABoolean of string
exception NotAnInt of string
exception MetaVariable
exception NotUnifiable of string * string
exception CouldNotSolve
exception UnknownFunctorialisation of string
exception NonMaximalFunctorialisation of string
exception FunctorialiseWithExplicit
exception ReservedName of string
exception WrongEntry
exception OptionsError
exception FatalError

let fatal s =
  Io.info (lazy (Printf.sprintf "The following error occurred: \n%s\n This is a bug, please report.\n%!" s));
  raise FatalError

let unsatisfiable_constraints t s =
  Io.info (lazy (Printf.sprintf "The constraints generated for the term %s could not be solved for the following reason:\n%s%!" t s));
  raise WrongEntry

let untypable t s =
  Io.info (lazy (Printf.sprintf "The term %s could not be typed for the following reason:\n%s%!" t s));
  raise WrongEntry

let not_valid_coherence c s =
  Io.info (lazy (Printf.sprintf "The coherence %s is not valid for the following reason:\n%s%!" c s));
  raise WrongEntry

let wrong_option_argument ~expected o a =
  Io.info (lazy (Printf.sprintf "Wrong argument for options %s, options %s given is not compatible with the expected type %s%!" o a expected));
  raise OptionsError

let incompatible_options o1 o2 =
  Io.info (lazy (Printf.sprintf "Incompatible options %s and %s%!" o1 o2));
  raise OptionsError

let unknown_option o =
  Io.info (lazy (Printf.sprintf "Unknown options %s%!" o));
  raise OptionsError
