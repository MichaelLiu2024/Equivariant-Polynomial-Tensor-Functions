(* ::Package:: *)

BeginPackage["EquivariantPolynomialTensorFunctions`"];


IsotypicComponentsTensorProduct::usage=
"IsotypicComponentsTensorProduct[\[Lambda],\[Mu]] returns a List of all isotypic components contained in the tensor product"


IsotypicComponentsTensorPower::usage=
"IsotypicComponentsTensorPower[\[Lambda],d] returns a List of all isotypic components contained in the tensor power"


IsotypicComponentsExteriorPower::usage=
"IsotypicComponentsExteriorPower[\[Lambda],d] returns a List of all isotypic components contained in exterior power"


IsotypicComponentsSchurPower::usage=
"IsotypicComponentsSchurPower[\[Lambda],p] returns a List of all isotypic components contained in the Schur power"


Begin["`Private`"];


SetAttributes[
{
IsotypicComponentsTensorProduct,
IsotypicComponentsTensorPower,
IsotypicComponentsExteriorPower
},
Listable
]


IsotypicComponentsTensorProduct[\[Lambda]_Integer?NonNegative,\[Mu]_Integer?NonNegative]:=Range[Abs[\[Lambda]-\[Mu]],\[Lambda]+\[Mu]]


IsotypicComponentsTensorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative]:=If[d==1,{\[Lambda]},Range[0,\[Lambda] d]]


IsotypicComponentsExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative]:=
Select[
IsotypicComponentsTensorPower[\[Lambda],d],
IsotypicMultiplicityExteriorPower[\[Lambda],d,#]>0&
]


IsotypicComponentsSchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ]:=
Select[
IsotypicComponentsTensorPower[\[Lambda],Total[p]],
IsotypicMultiplicitySchurPower[\[Lambda],p,#]>0&
]


End[];


EndPackage[];
