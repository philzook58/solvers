open Syntax

(*** First Order Formulas - Dec 2012 ***)
type fotrm =
    FOVar of string
  | FOFun of string * fotrm list
type foform = (*** assuming a single sort ***)
    FOEq of fotrm * fotrm
  | FOPred of string * fotrm list
  | FOImp of foform * foform
  | FOEqu of foform * foform
  | FOAll of string * foform
  | FOFal

exception NotFO

val foneg : foform -> foform
val trm_to_foform_stp : trm -> bool -> foform * stp option
val printf_fof : out_channel -> foform -> unit
val printf_fs : out_channel -> foform -> unit
