exception ReservedName of string
exception InvalidEntry
exception OptionsError
exception FatalError
exception UnknownId of string

let fatal s =
  Io.error "The following error occurred: \n%s\n This is a bug, please report.\n%!" s;
  raise FatalError

let unsatisfiable_constraints t s =
  Io.error "The constraints generated for the %s could not be solved for the following reason:\n%s%!" t s;
  raise InvalidEntry

let incomplete_constraints t =
  Io.error "Incomplete constraints: some of the meta-variable could not be resolved in the following %s%!" t;
  raise InvalidEntry

let untypable t s =
  Io.error"The %s could not be typed for the following reason:\n%s%!" t s;
  raise InvalidEntry

let not_valid_coherence c s =
  Io.error "The coherence %s is not valid for the following reason:\n%s%!" c s;
  raise InvalidEntry

let wrong_option_argument ~expected o a =
  Io.error "Wrong argument for options %s, options %s given is not compatible with the expected type %s%!" o a expected;
  raise OptionsError

let incompatible_options o1 o2 =
  Io.error "Incompatible options %s and %s%!" o1 o2;
  raise OptionsError

let unknown_option o =
  Io.error "Unknown options %s%!" o;
  raise OptionsError

let unknown_id s =
  Io.error "Identifier %s is unknown%!" s;
  raise InvalidEntry

let functorialisation t s =
  Io.error
    "Could not compute the functorialisation of %s for the following reason:\n%s%!" t s;
  raise InvalidEntry

let inversion t s =
  Io.error
    "Could not compute the inverse of %s for the following reason:\n%s%!" t s;
  raise InvalidEntry

let parsing_error t s =
  Io.error "Could not parse %s for the following reason:\n%s%!" t s;
  raise InvalidEntry
