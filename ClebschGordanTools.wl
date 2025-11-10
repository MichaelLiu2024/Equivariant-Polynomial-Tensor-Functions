(* ::Package:: *)

(* ::Title:: *)
(*ClebschGordanTools*)


(* ::Section:: *)
(*Public Functions*)


BeginPackage["ClebschGordanTools`",{"IsotypicDecompositionTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


PathBasisTensorProduct::usage=
"enumerates the path basis for Subscript[Hom, G](Subscript[H, \[Mu]],\!\(\*UnderscriptBox[\(\[CircleTimes]\), \(\[Lambda]\)]\)Subscript[H, \[Lambda]])"


PathBasisExteriorPower::usage=
"enumerates the path basis for Subscript[Hom, G](Subscript[H, \[Mu]],\[CapitalLambda]^d Subscript[H, \[Lambda]])"


PathBasisSymmetricPower::usage=
"enumerates the path basis for Subscript[Hom, G](Subscript[H, \[Mu]],\[ScriptCapitalS]^d Subscript[H, \[Lambda]])"


PathBasisSchurPower::usage=
"enumerates the path basis for Subscript[Hom, G](Subscript[H, \[Mu]],Subscript[e, \[Pi]] \!\(\*SubsuperscriptBox[\(H\), \(\[Lambda]\), \(\[CircleTimes]d\)]\))"


ClebschGordanTensor::usage=
"returns the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s)"


AntisymmetrizedClebschGordanTensor::usage=
"returns the antisymmetrized Clebsch-Gordan tensor CG((\[Lambda],...,\[Lambda]),\[Gamma]s)"


EvaluateClebschGordanTensor::usage=
"evaluates the Clebsch-Gordan tensor CG(\[Lambda]s,\[Gamma]s) at the inputs xs"


EvaluateSymmetrizedClebschGordanTensor::usage=
"evaluates the symmetrized Clebsch-Gordan tensor CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)"


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Declarations*)


MemoizedClebschGordanCoefficient::usage=
"is a memoized numerical version of the built-in function ClebschGordan"


MemoizedClebschGordanTensor::usage=
"returns the elementary Clebsch-Gordan tensor"


ClebschGordanCoefficient::usage=
"returns the iterated Clebsch-Gordan coefficient"


(* ::Subsection:: *)
(*Private Function Implementations*)


MemoizedClebschGordanCoefficient[\[Lambda]1_Integer?NonNegative,m1_Integer,\[Lambda]2_Integer?NonNegative,m2_Integer,\[Lambda]3_Integer?NonNegative,m3_Integer]:=
MemoizedClebschGordanCoefficient[\[Lambda]1,m1,\[Lambda]2,m2,\[Lambda]3,m3]=
N[ClebschGordan[{\[Lambda]1,m1},{\[Lambda]2,m2},{\[Lambda]3,m3}]]


MemoizedClebschGordanTensor[\[Lambda]1_Integer?NonNegative,\[Lambda]2_Integer?NonNegative,\[Lambda]3_Integer?NonNegative]:=
MemoizedClebschGordanTensor[\[Lambda]1,\[Lambda]2,\[Lambda]3]=
Chop@SparseArray[
Join@@Table[
{1+\[Lambda]1+m1,1+\[Lambda]2+m2,1+\[Lambda]3+m1+m2}->MemoizedClebschGordanCoefficient[\[Lambda]1,m1,\[Lambda]2,m2,\[Lambda]3,m1+m2],
{m1,-\[Lambda]1,\[Lambda]1},{m2,Max[-\[Lambda]2,-\[Lambda]3-m1],Min[\[Lambda]2,\[Lambda]3-m1]}
],
{2\[Lambda]1+1,2\[Lambda]2+1,2\[Lambda]3+1}
]


ClebschGordanCoefficient[\[Gamma]s_List?VectorQ,ms_List?VectorQ]:=
With[
{ss=Accumulate[ms]},
Times@@MapThread[MemoizedClebschGordanCoefficient,{Most[\[Gamma]s],Most[ss],ConstantArray[First[\[Gamma]s],Length[\[Gamma]s]-1],Rest[ms],Rest[\[Gamma]s],Rest[ss]}]
]


ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
ClebschGordanTensorTrain[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]:=MapThread[MemoizedClebschGordanTensor,{Most[\[Gamma]s],Rest[\[Lambda]s],Rest[\[Gamma]s]}]


temp[y_,{x_,tt_}]:=Dot[x,Dot[y,tt]]


(* ::Subsection:: *)
(*Public Function Attributes*)


SetAttributes[
{
PathBasisExteriorPower,
PathBasisSymmetricPower,
TensorBasisExteriorPower,
TensorBasisSymmetricPower
},
Listable
]


(* ::Subsection:: *)
(*Public Function Implementations*)


(*make a helper function so its clearer whats going on here*)
PathBasisTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=FoldList[Abs[#1-First[#2]]+Last[#2]-1&,First[\[Lambda]s],Transpose[{Rest[\[Lambda]s],#}]]&/@Position[Fold[IsotypicComponentsTensorProduct,\[Lambda]s],\[Mu]]


PathBasisExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
Switch[
d,
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+1-Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
];


PathBasisSymmetricPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]/;d<=3:=
Switch[
d,
1,{{\[Lambda]}},
2,{{\[Lambda],\[Mu]}},
3,{{\[Lambda],#+Mod[#,2]&@Abs[\[Lambda]-\[Mu]],\[Mu]}}
];


TensorBasisTensorProduct[\[Lambda]s_List?VectorQ,\[Mu]_Integer?NonNegative]:=ClebschGordanTensor[\[Lambda]s]/@PathBasisTensorProduct[\[Lambda]s,\[Mu]]


TensorBasisExteriorPower[\[Lambda]_Integer?NonNegative,d_Integer?NonNegative,\[Mu]_Integer?NonNegative]:=AntisymmetrizedClebschGordanTensor/@PathBasisExteriorPower[\[Lambda],d,\[Mu]]


ClebschGordanTensor[\[Lambda]s_List?VectorQ][\[Gamma]s_List?VectorQ]:=ClebschGordanTensor[\[Lambda]s,\[Gamma]s]
ClebschGordanTensor[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]:=
If[
Length[\[Lambda]s]==1,
IdentityMatrix[2First[\[Gamma]s]+1,SparseArray],
Chop@Dot@@ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]
]


AntisymmetrizedClebschGordanTensor[\[Gamma]s_List?VectorQ]:=
If[
Length[\[Gamma]s]==1,
IdentityMatrix[2First[\[Gamma]s]+1,SparseArray],
Module[
{\[Lambda]=First[\[Gamma]s],\[Mu]=Last[\[Gamma]s],d=Length[\[Gamma]s],msList,\[Lambda]s\[Mu]},

(*We could still try to generate these directly somehow...*)
msList=Select[Permutations[Range[-\[Lambda],\[Lambda]],{d}],-\[Gamma]s\[VectorLessEqual]Accumulate[#]\[VectorLessEqual]\[Gamma]s&];
\[Lambda]s\[Mu]=Append[ConstantArray[\[Lambda],d],\[Mu]];

Chop@Symmetrize[
SymmetrizedArray[
1+\[Lambda]s\[Mu]+Append[#,Total[#]]->ClebschGordanCoefficient[\[Gamma]s,#]&/@msList,
2\[Lambda]s\[Mu]+1
],
Antisymmetric[Range[d]]
]
]
]


EvaluateClebschGordanTensor[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ,xs_List?MatrixQ]:=Fold[temp,First[xs],Transpose[{Rest[xs],ClebschGordanTensorTrain[\[Lambda]s,\[Gamma]s]}]]


EvaluateSymmetrizedClebschGordanTensor[\[Lambda]_Integer?NonNegative,\[Gamma]s_List?VectorQ,x_List?VectorQ]:=EvaluateClebschGordanTensor[ConstantArray[\[Lambda],Length[\[Gamma]s]],\[Gamma]s,ConstantArray[x,Length[\[Gamma]s]]]


End[];


EndPackage[];
