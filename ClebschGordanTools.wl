(* ::Package:: *)

(* ::Title:: *)
(*ClebschGordanTools*)


(* ::Section:: *)
(*Public Functions*)


BeginPackage["ClebschGordanTools`",{"IsotypicDecompositionTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


(*Ensure everything is numerical; ensure numerical results are Chopped*)


ClebschGordanPathsTensorProduct::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the tensor product of the \[Lambda]s."


ClebschGordanPathsExteriorPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold exterior power of \[Lambda]."


ClebschGordanPathsSymmetricPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the d-fold symmetric power of \[Lambda]."


ClebschGordanPathsSchurPower::usage="gives a list of all Clebsch-Gordan paths from \[Mu] to the image of the Young symmetrizer p on \[Lambda]."


ClebschGordanTensorTrain::usage="gives the tensor train representation of the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)."


EvaluateClebschGordanTensorTrain::usage="evaluates the tensor train representation of CG(\[Lambda]s,\[Gamma]s) at the inputs xs."


EvaluateSymmetrizedClebschGordanTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."


ClebschGordanTensor::usage="gives the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)."


AntisymmetrizedClebschGordanTensor::usage="gives the antisymmetrized Clebsch-Gordan tensor CG((\[Lambda],...,\[Lambda]),\[Gamma]s)."


EvaluateClebschGordanTensor::usage="evaluates the tensor CG(\[Lambda]s,\[Gamma]s) at the inputs xs."


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


(*a memoized numerical version of the built-in function ClebschGordan*)
ElementaryClebschGordanCoefficient[\[Lambda]1_Integer?NonNegative,m1_Integer,\[Lambda]2_Integer?NonNegative,m2_Integer,\[Lambda]3_Integer?NonNegative,m3_Integer]:=
ElementaryClebschGordanCoefficient[\[Lambda]1,m1,\[Lambda]2,m2,\[Lambda]3,m3]=
N[ClebschGordan[{\[Lambda]1,m1},{\[Lambda]2,m2},{\[Lambda]3,m3}]]


(*gives the elementary Clebsch-Gordan tensor CG({\[Lambda]1,\[Lambda]2},{\[Lambda]1,\[Gamma]2})*)
ElementaryClebschGordanTensor[\[Lambda]1_Integer?NonNegative,\[Lambda]2_Integer?NonNegative,\[Lambda]3_Integer?NonNegative]:=
ElementaryClebschGordanTensor[\[Lambda]1,\[Lambda]2,\[Lambda]3]=
Chop[
SparseArray[
Join@@Table[
{1+\[Lambda]1+m1,1+\[Lambda]2+m2,1+\[Lambda]3+m1+m2}->ElementaryClebschGordanCoefficient[\[Lambda]1,m1,\[Lambda]2,m2,\[Lambda]3,m1+m2],
{m1,-\[Lambda]1,\[Lambda]1},{m2,Max[-\[Lambda]2,-\[Lambda]3-m1],Min[\[Lambda]2,\[Lambda]3-m1]}
],
{2\[Lambda]1+1,2\[Lambda]2+1,2\[Lambda]3+1}
]
]


(*gives the coefficient of the Clebsch-Gordan tensor CG((\[Gamma]1,...,\[Gamma]1),\[Gamma]s)*)
ClebschGordanCoefficient[\[Gamma]s_List?VectorQ,ms_List?VectorQ]:=
With[
{ss=Accumulate[ms]},
Times@@MapThread[ElementaryClebschGordanCoefficient,{Most[\[Gamma]s],Most[ss],ConstantArray[First[\[Gamma]s],Length[\[Gamma]s]-1],Rest[ms],Rest[\[Gamma]s],Rest[ss]}]
]


(*gives the contraction of the Clebsch-Gordan tensor cg with y in the first mode and x in the second mode*)
ContractClebschGordanLegs[y_?VectorQ,{x_List?VectorQ,cg_SparseArray}]:=Dot[x,Dot[y,cg]]


(*helper to convert indices into paths*)
\[Alpha]to\[Gamma][\[Gamma]_Integer?NonNegative,{\[Lambda]_Integer?NonNegative,\[Alpha]_Integer?NonNegative}]:=Abs[\[Gamma]-\[Lambda]]+\[Alpha]-1


(* ::Subsection:: *)
(*Public Function Attributes*)


SetAttributes[
{
ClebschGordanPathsExteriorPower,
ClebschGordanPathsSymmetricPower
},
Listable
]


(* ::Subsection:: *)
(*Public Function Implementations*)


ClebschGordanPathsTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=
Map[
Function[\[Alpha]s,FoldList[\[Alpha]to\[Gamma],First[\[Lambda]s],Transpose[{Rest[\[Lambda]s],\[Alpha]s}]]],
Position[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu]]
]


ClebschGordanPathsExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
Switch[
d,
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+1-Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
];


ClebschGordanPathsSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
Switch[
d,
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
];


ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]:=MapThread[ElementaryClebschGordanTensor,{Most[\[Gamma]s],Rest[\[Lambda]s],Rest[\[Gamma]s]}]


EvaluateClebschGordanTensorTrain[xs_List,tt_List]:=Chop@Fold[ContractClebschGordanLegs,First[xs],Transpose[{Rest[xs],tt}]]


EvaluateSymmetrizedClebschGordanTensorTrain[x_List?VectorQ,tt_List]:=EvaluateClebschGordanTensorTrain[ConstantArray[x,Length[tt]+1],tt]


(*Maybe this should take the tensor train as input? unclear.*)
ClebschGordanTensor[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensor[\[Lambda]s,\[Gamma]s]
ClebschGordanTensor[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]:=
If[
Length[\[Lambda]s]==1,(*we should remove calls with length 1 eventually by adjusting code higher up*)
IdentityMatrix[2First[\[Gamma]s]+1,SparseArray],
Chop@Dot@@ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
]


(*Explicitly implement the case legnth=3 as well. Separate into legnth <=3 and length >=4 cases for clarity*)
AntisymmetrizedClebschGordanTensor[\[Gamma]s_List?VectorQ]/;Length[\[Gamma]s]<=3:=
Switch[
Length[\[Gamma]s],
1,IdentityMatrix[2First[\[Gamma]s]+1,SparseArray],
2,If[EvenQ[\[Gamma]s[[2]]],0,ClebschGordanTensor[ConstantArray[First[\[Gamma]s],2],\[Gamma]s]],
_,Module[
{\[Lambda]=First[\[Gamma]s],\[Mu]=Last[\[Gamma]s],d=Length[\[Gamma]s],msList,\[Lambda]s\[Mu]},

(*We could still try to generate these directly somehow...*)
msList=Select[Permutations[Range[-\[Lambda],\[Lambda]],{d}],-\[Gamma]s\[VectorLessEqual]Accumulate[#]\[VectorLessEqual]\[Gamma]s&];
\[Lambda]s\[Mu]=Append[ConstantArray[\[Lambda],d],\[Mu]];

Chop[
Symmetrize[
SymmetrizedArray[
1+\[Lambda]s\[Mu]+Append[#,Total[#]]->ClebschGordanCoefficient[\[Gamma]s,#]&/@msList,
2\[Lambda]s\[Mu]+1
],
Antisymmetric[Range[d]]
]
]
]
]


EvaluateClebschGordanTensor[xs_List,tensor_]:=Chop@Normal@Fold[Dot[#2,#1]&,tensor,Take[xs,TensorRank[tensor]-1]]


End[];


EndPackage[];
