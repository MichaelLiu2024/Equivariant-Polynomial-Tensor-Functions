(* ::Package:: *)

BeginPackage["IsotypicDecompositionTools`",{"CombinatoricsTools`"}];


IsotypicComponentTensorProductQ
IsotypicMultiplicityTensorProduct
IsotypicMultiplicityExteriorPower
IsotypicMultiplicitySchurPower
IsotypicComponentsTensorProduct
IsotypicComponentsTensorPower
IsotypicComponentsExteriorPower
IsotypicComponentsSchurPower


Begin["`Private`"];


(* ::Subsubsection:: *)
(*Public Functions*)


IsotypicComponentTensorProductQ::usage="gives True if \[Mu] is an isotypic component in the tensor product \!\(\*UnderscriptBox[\(\[CircleTimes]\), \(\[Lambda] \[Element] \[Lambda]s\)]\)\!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)."
IsotypicComponentTensorProductQ[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=With[{m=Max[\[Lambda]s],s=Total[\[Lambda]s]},Max[0,2m-s]<=\[Mu]<=s]


IsotypicMultiplicityTensorProduct::usage="gives the isotypic multiplicity of \[Mu] in the tensor product \!\(\*UnderscriptBox[\(\[CircleTimes]\), \(\[Lambda] \[Element] \[Lambda]s\)]\)\!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)."
IsotypicMultiplicityTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=Count[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu],{-1}]


IsotypicMultiplicityExteriorPower::usage="gives the isotypic multiplicity of \[Mu] in the exterior power \!\(\*SuperscriptBox[\(\[CapitalLambda]\), \(d\)]\)\!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)."
IsotypicMultiplicityExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]:=Count[#,_?(Total[#]==\[Mu]&)]-Count[#,_?(Total[#]==\[Mu]+1&)]&@Subsets[Range[-\[Lambda],\[Lambda]],{d}]


IsotypicMultiplicitySchurPower::usage="gives the isotypic multiplicity of \[Mu] in the Schur power \!\(\*SubscriptBox[\(e\), \(p\)]\)\!\(\*SubsuperscriptBox[\(H\), \(\[Lambda]\), \(\[CircleTimes]d\)]\)."
IsotypicMultiplicitySchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ,\[Mu]_Integer?NonNegative]:=Module[{x},Coefficient[#,x,\[Mu]]-Coefficient[#,x,\[Mu]+1]&@SchurS[ConjugatePartition@p,x^Range[-\[Lambda],\[Lambda]]]]


IsotypicComponentsTensorProduct::usage="gives a list of all isotypic components contained in the tensor product \!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)\[CircleTimes]\!\(\*SubscriptBox[\(H\), \(\[Mu]\)]\)."
SetAttributes[IsotypicComponentsTensorProduct,Listable]
IsotypicComponentsTensorProduct[\[Lambda]_Integer?NonNegative][\[Mu]_Integer?NonNegative]:=IsotypicComponentsTensorProduct[\[Lambda],\[Mu]]
IsotypicComponentsTensorProduct[\[Lambda]_Integer?NonNegative,\[Mu]_Integer?NonNegative]:=Range[Abs[\[Lambda]-\[Mu]],\[Lambda]+\[Mu]]


IsotypicComponentsTensorPower::usage="gives a list of all isotypic components contained in the tensor power \!\(\*SubsuperscriptBox[\(H\), \(\[Lambda]\), \(\[CircleTimes]d\)]\)."
SetAttributes[IsotypicComponentsTensorPower,Listable]
IsotypicComponentsTensorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative]:=If[d==1,{\[Lambda]},Range[0,\[Lambda] d]]


IsotypicComponentsExteriorPower::usage="gives a list of all isotypic components contained in exterior power \!\(\*SuperscriptBox[\(\[CapitalLambda]\), \(d\)]\)\!\(\*SubscriptBox[\(H\), \(\[Lambda]\)]\)."
SetAttributes[IsotypicComponentsExteriorPower,Listable]
IsotypicComponentsExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative]:=
 Select[
  IsotypicComponentsTensorPower[\[Lambda],d],
  IsotypicMultiplicityExteriorPower[\[Lambda],d,#]>0&
 ]


IsotypicComponentsSchurPower::usage="gives a list of all isotypic components contained in the Schur power \!\(\*SubscriptBox[\(e\), \(p\)]\)\!\(\*SubsuperscriptBox[\(H\), \(\[Lambda]\), \(\[CircleTimes]d\)]\)."
IsotypicComponentsSchurPower[\[Lambda]_Integer?NonNegative,p_List?VectorQ]:=
 Select[
  IsotypicComponentsTensorPower[\[Lambda],Total[p]],
  IsotypicMultiplicitySchurPower[\[Lambda],p,#]>0&
 ]


End[];


EndPackage[];
