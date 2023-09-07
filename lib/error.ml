exception NotValid
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

let fatal s =
  Io.printf "The following error occurred. This is an issue of the software, please report.\n";
  Io.printf s;
  Io.print_newline();
  assert false

let constraints t s =
  Io.printf "The constraints generated for the term %s could not be solved for the following reason:\n" t;
  Io.printf s;
  Io.print_newline();
  raise WrongEntry

let untypable t s =
  Io.printf "The term %s could not be typed for the following reason:\n" t;
  Io.printf s;
  Io.print_newline();
  raise WrongEntry

let not_valid_coherence c s =
  Io.printf "The coherence %s is not valid for the following reason:\n" c;
  Io.printf s;
  Io.print_newline();
  raise WrongEntry

let wrong_option_argument ~expected o a =
  Io.printf "Wrong argument for options %s, options %s given is not compatible with the expected type %s\n" o a expected;
  raise OptionsError

let incompatible_options o1 o2 =
  Io.printf "Incompatible options %s and %s\n" o1 o2;
  raise OptionsError

let unknown_options o =
  Io.printf "Unknown options %s\n" o;
  raise OptionsError
