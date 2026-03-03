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
] :=

Positive @ n \[And] IntegerQ @ n


NonNegativeIntegerQ[
 n_
] :=

NonNegative @ n \[And] IntegerQ @ n


NonPositiveIntegerQ[
 n_
] :=

NonPositive @ n \[And] IntegerQ @ n


NegativeIntegerQ[
 n_
] :=

Negative @ n \[And] IntegerQ @ n


PositiveIntegersQ[
 ns_
] :=

VectorQ[ns, PositiveIntegerQ]


NonNegativeIntegersQ[
 ns_
] :=

VectorQ[ns, NonNegativeIntegerQ]


NonPositiveIntegersQ[
 ns_
] :=

VectorQ[ns, NonPositiveIntegerQ]


NegativeIntegersQ[
 ns_
] :=

VectorQ[ns, NegativeIntegerQ]


DistinctPositiveIntegersQ[
 ns_
] :=

DuplicateFreeQ @ ns \[And] PositiveIntegersQ @ ns


DistinctNonNegativeIntegersQ[
 ns_
] :=

DuplicateFreeQ @ ns \[And] NonNegativeIntegersQ @ ns


DistinctNonPositiveIntegersQ[
 ns_
] :=

DuplicateFreeQ @ ns \[And] NonPositiveIntegersQ @ ns


DistinctNegativeIntegersQ[
 ns_
] :=

DuplicateFreeQ @ ns \[And] NegativeIntegersQ @ ns


IntegerPartitionQ[
 p_
] :=

NonNegativeIntegersQ @ p \[And] NonPositiveIntegersQ @ Differences @ p


IntegerPartitionsQ[
 ps_
] :=

ListQ @ ps \[And] AllTrue[ps, IntegerPartitionQ]


End[];


EndPackage[];
