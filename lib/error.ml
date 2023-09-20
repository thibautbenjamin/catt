exception UnknownOption of string
exception NotABoolean of string
exception NotAnInt of string
exception NotUnifiable of string * string
exception CouldNotSolve
exception UnknownFunctorialisation of string
exception NonMaximalFunctorialisation of string
exception FunctorialiseWithExplicit
exception ReservedName of string

exception InvalidEntry
exception OptionsError
exception FatalError
exception UnknownId of string

let fatal s =
  Io.info (lazy (Printf.sprintf "The following error occurred: \n%s\n This is a bug, please report.\n%!" s));
  raise FatalError

let unsatisfiable_constraints t s =
  Io.info (lazy (Printf.sprintf "The constraints generated for the %s could not be solved for the following reason:\n%s%!" t s));
  raise InvalidEntry

let incomplete_constraints t =
  Io.info (lazy (Printf.sprintf "Incomplete constraints: some of the meta-variable could not be resolved in the following %s%!" t));
  raise InvalidEntry

let untypable t s =
  Io.info (lazy (Printf.sprintf "The %s could not be typed for the following reason:\n%s%!" t s));
  raise InvalidEntry

let not_valid_coherence c s =
  Io.info (lazy (Printf.sprintf "The coherence %s is not valid for the following reason:\n%s%!" c s));
  raise InvalidEntry

let wrong_option_argument ~expected o a =
  Io.info (lazy (Printf.sprintf "Wrong argument for options %s, options %s given is not compatible with the expected type %s%!" o a expected));
  raise OptionsError

let incompatible_options o1 o2 =
  Io.info (lazy (Printf.sprintf "Incompatible options %s and %s%!" o1 o2));
  raise OptionsError

let unknown_option o =
  Io.info (lazy (Printf.sprintf "Unknown options %s%!" o));
  raise OptionsError

let unknown_id s =
  Io.info (lazy (Printf.sprintf "Identifier %s is unknown%!" s));
  raise InvalidEntry
