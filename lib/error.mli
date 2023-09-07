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

val fatal : (unit, unit, string, unit) format4 -> 'a
val untypable : string -> (unit, unit, string, unit) format4 -> 'a
val not_valid_coherence : string -> (unit, unit, string, unit) format4 -> 'a
