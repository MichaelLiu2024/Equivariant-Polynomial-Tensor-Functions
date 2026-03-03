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

DistinctPositiveIntegersQ
DistinctNonNegativeIntegersQ
DistinctNonPositiveIntegersQ
DistinctNegativeIntegersQ

IntegerPartitionQ

IntegerPartitionsQ


Begin["`Private`"];


PositiveIntegerQ[
 n_
] /;
True
:=

Positive @ n \[And] IntegerQ @ n


NonNegativeIntegerQ[
 n_
] /;
True
:=

NonNegative @ n \[And] IntegerQ @ n


NonPositiveIntegerQ[
 n_
] /;
True
:=

NonPositive @ n \[And] IntegerQ @ n


NegativeIntegerQ[
 n_
] /;
True
:=

Negative @ n \[And] IntegerQ @ n


PositiveIntegersQ[
 ns_
] /;
True
:=

VectorQ[ns, PositiveIntegerQ]


NonNegativeIntegersQ[
 ns_
] /;
True
:=

VectorQ[ns, NonNegativeIntegerQ]


NonPositiveIntegersQ[
 ns_
] /;
True
:=

VectorQ[ns, NonPositiveIntegerQ]


NegativeIntegersQ[
 ns_
] /;
True
:=

VectorQ[ns, NegativeIntegerQ]


DistinctPositiveIntegersQ[
 ns_
] /;
True
:=

DuplicateFreeQ @ ns \[And] PositiveIntegersQ @ ns


DistinctNonNegativeIntegersQ[
 ns_
] /;
True
:=

DuplicateFreeQ @ ns \[And] NonNegativeIntegersQ @ ns


DistinctNonPositiveIntegersQ[
 ns_
] /;
True
:=

DuplicateFreeQ @ ns \[And] NonPositiveIntegersQ @ ns


DistinctNegativeIntegersQ[
 ns_
] /;
True
:=

DuplicateFreeQ @ ns \[And] NegativeIntegersQ @ ns


IntegerPartitionQ[
 p_
] /;
True
:=

NonNegativeIntegersQ @ p \[And] NonPositiveIntegersQ @ Differences @ p


IntegerPartitionsQ[
 ps_
] /;
True
:=

ListQ @ ps \[And] AllTrue[ps, IntegerPartitionQ]


End[];


EndPackage[];
