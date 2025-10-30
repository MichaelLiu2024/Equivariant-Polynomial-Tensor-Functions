(* ::Package:: *)

(* ::Section:: *)
(*Public Functions*)


BeginPackage["ClebschGordanTools`"];


(* ::Subsection:: *)
(*Public Function Declarations*)


ClebschGordanTensor::usage=
"ClebschGordanTensor[\[Lambda]s,\[Gamma]s] returns the Clebsch-Gordan tensor traveling along \[Lambda]s via the path \[Gamma]s"


AntisymmetrizedClebschGordanTensor::usage=
"AntisymmetrizedClebschGordanTensor[\[Gamma]s] returns the antisymmetrized Clebsch-Gordan tensor traveling along ConstantArray[First[\[Gamma]s],Length[\[Gamma]s]] via the path \[Gamma]s"


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Declarations*)


MemoizedClebschGordanCoefficient::usage=
"MemoizedClebschGordanCoefficient[\[Lambda]1,m1,\[Lambda]2,m2,\[Lambda]3,m3] is a memoized numerical version of the built-in function ClebschGordan"


MemoizedClebschGordanTensor::usage=
"MemoizedClebschGordanTensor[\[Lambda]1,\[Lambda]2,\[Lambda]3] returns the Clebsch-Gordan tensor"


ClebschGordanCoefficient::usage=
"ClebschGordanCoefficient[\[Gamma]s,ms] returns the Clebsch-Gordan coefficient"


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


AntisymmetrizeRows[tensor_List,p_List?VectorQ]:=Symmetrize[tensor,Antisymmetric/@YoungTableau@p]


SymmetrizeColumns[tensor_List,p_List?VectorQ]:=Symmetrize[tensor,Symmetric/@ConjugateTableau@YoungTableau@p]


YoungSymmetrize[tensor_List,p_List?VectorQ]:=SymmetrizeColumns[AntisymmetrizeRows[tensor,p],p]


(* ::Subsection:: *)
(*Public Function Implementations*)


ClebschGordanTensor[\[Lambda]s_List?VectorQ,\[Gamma]s_List?VectorQ]:=
If[
Length[\[Lambda]s]==1,
IdentityMatrix[2First[\[Gamma]s]+1,SparseArray],
Chop@Dot@@MapThread[MemoizedClebschGordanTensor,{Most[\[Gamma]s],Rest[\[Lambda]s],Rest[\[Gamma]s]}]
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


End[];


EndPackage[];
