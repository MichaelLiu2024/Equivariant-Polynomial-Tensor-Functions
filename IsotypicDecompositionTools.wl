(* ::Package:: *)

BeginPackage["IsotypicDecompositionTools`",{"CombinatoricsTools`"}];


IsotypicComponentsTensorProduct
IsotypicComponentsTensorPower
IsotypicComponentsExteriorPower
IsotypicComponentsSchurPower
ConstrainedIsotypicComponentsExteriorPowers
ConstrainedIsotypicComponentsSchurPowers


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Private Functions*)


IsotypicComponentTensorProductQ::usage="gives True if \[Mu] is an isotypic component in the tensor product \!\(\*UnderscriptBox[\(\[CircleTimes]\), \(\[Lambda] \[Element] \[Lambda]s\)]\)\!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)."
IsotypicComponentTensorProductQ[\[Lambda]s_List?VectorQ,\[Mu]_?NonNegativeIntegerQ]:=
 With[
  {m=Max[\[Lambda]s],s=Total[\[Lambda]s]},
  Max[0,2m-s]<=\[Mu]<=s
 ]


IsotypicMultiplicityExteriorPower::usage="gives the isotypic multiplicity of \[Mu] in the exterior power \!\(\*SuperscriptBox[\(\[CapitalLambda]\), \(d\)]\)\!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)."
IsotypicMultiplicityExteriorPower[\[Lambda]_?NonNegativeIntegerQ,d_?NonNegativeIntegerQ,\[Mu]_?NonNegativeIntegerQ]:=
 Count[#,_?(Total[#]==\[Mu]&)]-Count[#,_?(Total[#]==\[Mu]+1&)]&@Subsets[Range[-\[Lambda],\[Lambda]],{d}]


IsotypicMultiplicitySchurPower::usage="gives the isotypic multiplicity of \[Mu] in the Schur power \!\(\*SubscriptBox[\(e\), \(p\)]\)\!\(\*SubsuperscriptBox[\(H\), \(\[Lambda]\), \(\[CircleTimes]d\)]\)."
IsotypicMultiplicitySchurPower[\[Lambda]_?NonNegativeIntegerQ,p_List?VectorQ,\[Mu]_?NonNegativeIntegerQ]:=
 With[
  {q=Unique@q},
  {poly=SchurS[ConjugatePartition@p,q,\[Lambda]]},
  SeriesCoefficient[poly,{q,0,\[Mu]}]-SeriesCoefficient[poly,{q,0,\[Mu]+1}]
 ]


(* ::Subsubsection:: *)
(*Public Functions*)


IsotypicComponentsTensorProduct::usage="gives a list of all isotypic components contained in the tensor product \!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)\[CircleTimes]\!\(\*SubscriptBox[\(H\), \(\[Mu]\)]\)."
SetAttributes[IsotypicComponentsTensorProduct,Listable]
IsotypicComponentsTensorProduct[\[Lambda]_?NonNegativeIntegerQ,\[Mu]_?NonNegativeIntegerQ]:=
 Range[
  Abs[\[Lambda]-\[Mu]],
  \[Lambda]+\[Mu]
 ]


IsotypicComponentsTensorPower::usage="gives a list of all isotypic components contained in the tensor power \!\(\*SubsuperscriptBox[\(H\), \(\[Lambda]\), \(\[CircleTimes]d\)]\)."
SetAttributes[IsotypicComponentsTensorPower,Listable]
IsotypicComponentsTensorPower[\[Lambda]_?NonNegativeIntegerQ,d_?NonNegativeIntegerQ]:=
 If[
  d==1,
  {\[Lambda]},
  Range[0,\[Lambda]*d]
 ]


IsotypicComponentsExteriorPower::usage="gives a list of all isotypic components contained in exterior power \!\(\*SuperscriptBox[\(\[CapitalLambda]\), \(d\)]\)\!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)."
SetAttributes[IsotypicComponentsExteriorPower,Listable]
IsotypicComponentsExteriorPower[\[Lambda]_?NonNegativeIntegerQ,d_?NonNegativeIntegerQ]:=
 Select[
  IsotypicComponentsTensorPower[\[Lambda],d],
  IsotypicMultiplicityExteriorPower[\[Lambda],d,#]>0&
 ]


IsotypicComponentsSchurPower::usage="gives a list of all isotypic components contained in the Schur power \!\(\*SubscriptBox[\(e\), \(p\)]\)\!\(\*SubsuperscriptBox[\(H\), \(\[Lambda]\), \(\[CircleTimes]d\)]\)."
IsotypicComponentsSchurPower[\[Lambda]s_List?VectorQ,\[Pi]\[Lambda]s_List]:=MapThread[IsotypicComponentsSchurPower,{\[Lambda]s,\[Pi]\[Lambda]s}]
IsotypicComponentsSchurPower[\[Lambda]_?NonNegativeIntegerQ,p_List?VectorQ]:=
 Select[
  IsotypicComponentsTensorPower[\[Lambda],Total@p],
  IsotypicMultiplicitySchurPower[\[Lambda],p,#]>0&
 ]


ConstrainedIsotypicComponentsExteriorPowers[\[Lambda]_?NonNegativeIntegerQ,p_List?VectorQ,\[Mu]_?NonNegativeIntegerQ]:=
 Select[
  Tuples@IsotypicComponentsExteriorPower[\[Lambda],p],
  IsotypicComponentTensorProductQ[#,\[Mu]]&
 ]


ConstrainedIsotypicComponentsSchurPowers[\[Lambda]s_List?VectorQ,\[Pi]\[Lambda]s_List,\[Mu]_?NonNegativeIntegerQ]:=
 Select[
  Tuples@IsotypicComponentsSchurPower[\[Lambda]s,\[Pi]\[Lambda]s],
  IsotypicComponentTensorProductQ[#,\[Mu]]&
 ]


End[];


EndPackage[];
