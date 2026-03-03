(* ::Package:: *)

BeginPackage["BooleanTools`"];


PositiveIntegerQ
NonNegativeIntegerQ
NonPositiveIntegerQ
NegativeIntegerQ

PositiveIntegersQ
NonNegativeIntegersQ
NonPositiveIntegersQ
NegativeIntegersQ

IntegerPartitionQ

IntegerPartitionsQ


Begin["`Private`"];


PositiveIntegerQ[n_] := Positive@n \[And] IntegerQ@n


NonNegativeIntegerQ[n_] := NonNegative@n \[And] IntegerQ@n


NonPositiveIntegerQ[n_] := NonPositive@n \[And] IntegerQ@n


NegativeIntegerQ[n_] := Negative@n \[And] IntegerQ@n





PositiveIntegersQ[ns_] := VectorQ[ns,PositiveIntegerQ]


NonNegativeIntegersQ[ns_] := VectorQ[ns,NonNegativeIntegerQ]


NonPositiveIntegersQ[ns_] := VectorQ[ns,NonPositiveIntegerQ]


NegativeIntegersQ[ns_] := VectorQ[ns,NegativeIntegerQ]





IntegerPartitionQ[p_] := NonNegativeIntegersQ@p \[And] NonPositiveIntegersQ@Differences@p





IntegerPartitionsQ[ps_] := ListQ@ps \[And] AllTrue[ps,IntegerPartitionQ]





End[];


EndPackage[];
