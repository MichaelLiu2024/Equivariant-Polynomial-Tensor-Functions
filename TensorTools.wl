(* ::Package:: *)

(* ::Title:: *)
(*TensorTools*)


(* ::Section:: *)
(*Public Functions*)


BeginPackage["TensorTools`",{"CombinatoricsTools`"}];


(* ::Subsection:: *)
(*Public Function Declarations*)


ContractLeafVectorsCoreTensorTrain::usage="evaluates the tensor train representation of CG(\[Lambda]s,\[Gamma]s) at the given legs."


EvaluateSymmetrizedTensorTrain::usage="evaluates the symmetrized tensor train representation of CG((\[Lambda],...,\[Lambda]),\[Gamma]s) at the inputs (x,...,x)."


ContractLeafVectorsCoreTensor::usage="evaluates the tensor CG(\[Lambda]s,\[Gamma]s) at the given legs."


ContractLeafSSYTCoreTensor


ContractLeafTensorsCoreTensorTrain


ContractCoreTensorTrain


EvaluateYoungSymmetrizedTensorTree


AntisymmetrizeRows


SymmetrizeColumns


YoungSymmetrize


(* ::Section:: *)
(*Private Functions*)


Begin["`Private`"];


(* ::Subsection:: *)
(*Private Function Implementations*)


ContractVectors[leafVector1_List?VectorQ,{leafVector2_List?VectorQ,coreTensor_?ArrayQ}]:=Dot[leafVector2,Dot[leafVector1,coreTensor]]


ContractTensors[leafTensor1_?ArrayQ,{leafTensor2_?ArrayQ,coreTensor_?ArrayQ}]:=
With[
{r1=TensorRank[leafTensor1],r2=TensorRank[leafTensor2]},
TensorContract[TensorProduct[leafTensor1,TensorContract[TensorProduct[leafTensor2,coreTensor],{{r2,r2+2}}]],{{r1,r1+r2}}]
]


(* ::Subsection:: *)
(*Public Function Implementations*)


ContractLeafVectorsCoreTensor[leafVectors_List][coreTensor_?ArrayQ]:=ContractLeafVectorsCoreTensor[leafVectors,coreTensor]
ContractLeafVectorsCoreTensor[leafVectors_List,coreTensor_?ArrayQ]:=Normal@Chop@Fold[Dot[#2,#1]&,coreTensor,Take[leafVectors,TensorRank[coreTensor]-1]]


ContractLeafSSYTCoreTensor[leafSSYT_List,coreTensor_?ArrayQ]:=
With[
{coreDimensions=Most@Dimensions@coreTensor},
{leafVectors=MapThread[With[{\[Lambda]=(#1-1)/2},Table[Subscript[Global`x, \[Lambda],m,#2],{m,-\[Lambda],\[Lambda]}]]&,{coreDimensions,Flatten[leafSSYT]}]},
ContractLeafVectorsCoreTensor[leafVectors,coreTensor]
]


ContractLeafVectorsCoreTensorTrain[leafVectors_List,coreTensorTrain_List]:=
If[
Length[leafVectors]==1,
Dot[First@leafVectors,First@coreTensorTrain],
Chop@Fold[ContractVectors,First[leafVectors],Transpose[{Rest[leafVectors],coreTensorTrain}]]
]


ContractLeafSSYTCoreTensorTrain[leafSSYT_List,coreTensorTrain_List]:=
With[
{coreDimensions=First@*Rest@*Dimensions/@coreTensorTrain},
{leafVectors=MapThread[With[{\[Lambda]=(#1-1)/2},Table[Subscript[Global`x, \[Lambda],m,#2],{m,-\[Lambda],\[Lambda]}]]&,{coreDimensions,Flatten[leafSSYT]}]},
ContractLeafVectorsCoreTensorTrain[leafVectors,coreTensorTrain]
]


ContractLeafTensorsCoreTensorTrain[leafTensors_List,coreTensorTrain_List]:=
If[
Length[leafTensors]==1,
Chop@Dot@@Join[leafTensors,coreTensorTrain],
Chop@Fold[ContractTensors,First[leafTensors],Transpose[{Rest[leafTensors],coreTensorTrain}]]
]


ContractCoreTensorTrain[coreTensorTrain_List]:=Chop@Dot@@coreTensorTrain


EvaluateSymmetrizedTensorTrain[leafVector_List?VectorQ,coreTensorTrain_List]:=Chop@Fold[Dot[leafVector,Dot[#1,#2]]&,leafVector,coreTensorTrain]


(*This is really a generalized Tucker format...*)
EvaluateYoungSymmetrizedTensorTree[leafVectors_List,leafTensors_List,coreTensorTrain_List]:=ContractLeafVectorsCoreTensorTrain[ContractLeafVectorsCoreTensor[leafVectors]/@leafTensors,coreTensorTrain]


AntisymmetrizeRows[tensor_?ArrayQ,p_List?VectorQ]:=Symmetrize[tensor,Antisymmetric/@YoungTableau@p]


SymmetrizeColumns[p_List?VectorQ][tensor_?ArrayQ]:=SymmetrizeColumns[tensor,p]
SymmetrizeColumns[tensor_?ArrayQ,p_List?VectorQ]:=Symmetrize[tensor,Symmetric/@ConjugateTableau@YoungTableau@p]


YoungSymmetrize[tensor_?ArrayQ,p_List?VectorQ]:=SymmetrizeColumns[AntisymmetrizeRows[tensor,p],p]


End[];


EndPackage[];
