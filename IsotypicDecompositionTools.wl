(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["IsotypicDecompositionTools`",{"CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


IsotypicComponentTensorProductQ::usage=
"IsotypicComponentTensorProductQ[\[Lambda]s,\[Mu]] returns True if \[Mu] is an isotypic component in the tensor product"


IsotypicMultiplicityExteriorPower::usage=
"IsotypicMultiplicityExteriorPower[\[Lambda],d,\[Mu]] returns the isotypic multiplicity of \[Mu] in the exterior power"


IsotypicMultiplicitySchurPower::usage=
"IsotypicMultiplicitySchurPower[\[Lambda],p,\[Mu]] returns the isotypic multiplicity of \[Mu] in the Schur power"


IsotypicComponentsTensorProduct::usage=
"IsotypicComponentsTensorProduct[\[Lambda],\[Mu]] returns a List of all isotypic components contained in the tensor product"


IsotypicComponentsTensorPower::usage=
"IsotypicComponentsTensorPower[\[Lambda],d] returns a List of all isotypic components contained in the tensor power"


IsotypicComponentsExteriorPower::usage=
"IsotypicComponentsExteriorPower[\[Lambda],d] returns a List of all isotypic components contained in exterior power"


IsotypicComponentsSchurPower::usage=
"IsotypicComponentsSchurPower[\[Lambda],p] returns a List of all isotypic components contained in the Schur power"


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Public Function Implementations*)


SetAttributes[
{
IsotypicComponentsTensorProduct,
IsotypicComponentsTensorPower,
IsotypicComponentsExteriorPower
},
Listable
]


IsotypicComponentTensorProductQ[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=With[{m=Max[\[Lambda]s],s=Total[\[Lambda]s]},Max[0,2m-s]<=\[Mu]<=s]


IsotypicMultiplicityExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]:=Count[#,_?(Total[#]==\[Mu]&)]-Count[#,_?(Total[#]==\[Mu]+1&)]&@Subsets[Range[-\[Lambda],\[Lambda]],{d}]


IsotypicMultiplicitySchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ,\[Mu]_Integer?NonNegative]:=Module[{x},Coefficient[#,x,\[Mu]]-Coefficient[#,x,\[Mu]+1]&@SchurS[ConjugatePartition@p,x^Range[-\[Lambda],\[Lambda]]]]


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
