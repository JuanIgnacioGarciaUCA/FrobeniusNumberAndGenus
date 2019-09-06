(* ::Package:: *)

BeginPackage["FrobeniusNumberAndGenus`"];


Authors="J.I. Garc\[IAcute]a-Garc\[IAcute]a D. Mar\[IAcute]n-Arag\[OAcute]n and A. Vigneron-Tenorio,
\nDpto. Matem\[AAcute]ticas,
Universidad de C\[AAcute]diz
ignacio.garcia@uca.es, daniel.marinaragon@alum.uca.es, alberto.vigneron@uca.es\n
";


Commands="This package defines the commands:
ComputeMinimumGenusLme,
MinFrob,FrobeniusEmbeddingDimensionMultiplicity,
ComputeEquivalenceClass.
Try command::usage for more help";


ComputeMinimumGenusLme::usage="Returns the least genus and the semigroups that have
this genus with a fixed multiplicity and embedding dimension\nExample: Algorithm1[5,3]\n";
MinFrob::usage="Returns the least Frobenius number of a numerical
semigroup of a fixed embedding dimension and multiplicity\nExample:
MinFrob[4,2]\n";
FrobeniusEmbeddingDimensionMultiplicity::usage="Returns the numerical
semigroups with minimal Frobenius number and fixed embedding dimension
and multiplicity\nExample:FrobeniusEmbeddingDimensionMultiplicity[11,2,4]\n";
ComputeEquivalenceClass::usage="Return the semigroups an equivalence class such
that their Frobenius number is minimum\nExample: Algorithm3[{6,7,8,9,11}]\n";


Print[Authors<>"\n"<>Commands];


Begin["`Private`"];


smgS[sgS1_]:=Module[{smgS={},i,aux,sgS},sgS=Sort[sgS1];
sgS=DeleteDuplicates[sgS];
If[Length[sgS]==1,Return[sgS]];
AppendTo[smgS,sgS[[1]]];
For[i=2,i<=Length[sgS],i++,If[Mod[sgS[[i]],smgS[[1]]]!=0,AppendTo[smgS,sgS[[i]]];
Break[];];];
For[,i<=Length[sgS],i++,If[FrobeniusSolve[smgS,sgS[[i]]]=={},AppendTo[smgS,sgS[[i]]]];];
Return[smgS]]

quitaElementoMinimal[{1},1]:={2,3}
quitaElementoMinimal[smg_,x_]:=Module[{saux,pos,m,i,laux},saux=smg;
pos=Position[saux,x][[1,1]];
saux=Delete[saux,pos];
saux=Sort[saux];
m=saux[[1]];
laux=Table[x+saux[[i]],{i,1,Length[saux]}];
saux=saux~Join~({2x,3x}~Join~laux);
Return[smgS[saux]];];


ComputeSons[smg_]:=Module[{i,sons={}},
	For[i=1,i<=Length[smg],i++,
		AppendTo[sons,quitaElementoMinimal[smg,smg[[i]]]];
	];
	Return[sons]
]


Stop[A_,m_,e_]:=Module[{i,list={}},
	For[i=1,i<=Length[A],i++,
		If[A[[i,1]]==m && Length[A[[i]]]==e,
			AppendTo[list,A[[i]]];
		];
	];
	Return[list];
]


ComputeMinimumGenusLme[m_,e_]:=Module[{k,A,list,i,CS={}},
	k = 0;
	A = {Table[i,{i,m,2m-1}]};
	While[True && k<=10,
		list = Stop[A,m,e];
		If[list != {},
			Return[{m-1+k,list}];
		];
		For[i=1,i<=Length[A],i++,
			CS = Join[CS,ComputeSons[A[[i]]]];
			CS = DeleteDuplicates[CS];
		];
		A = CS;
		k++;
	];
]


Step2[A_,\[Alpha]_,mm_]:=Module[{n,i,smg,fn,m,j,CC},
	CC={};
	n=Length[A];
	For[i=1,i<=n,i++,
		smg=A[[i,1]];
		fn=A[[i,2]];
		m = Length[smg];
		For[j=1,j<=m,j++,
			If[smg[[j]]>fn && smg[[j]]<=\[Alpha] && smg[[j]]!=mm,
				AppendTo[CC,{quitaElementoMinimal[smg,smg[[j]]],smg[[j]]}];	
			];
		];
	];
	Return[CC];
]


MinFrob[m_,e_]:=Module[{AA,II,CC,\[Alpha]\[Alpha],KK,BB},
	AA = {{Table[i,{i,m,2m-1}],m-1}};
	II = {};
	\[Alpha]\[Alpha] = Ceiling[(m-1)/(e-1)]m-1;
	(*Print["A=",AA];
	Print["\[Alpha]=",\[Alpha]\[Alpha]];*)

	While[True,
		CC=Step2[AA,\[Alpha]\[Alpha],m];
		KK=Select[CC,Length[#[[1]]]>=e&];
		
		(*Print["C=",CC];
		Print["K=",KK];*)
	
		If[KK=={},If[II=={},II=AA];Return[II[[1,2]]]];
		AA = KK;
(*Print[AA];*)
		BB = Select[KK,Length[#[[1]]]==e&];
(*Print["B=",BB];*)
		If[BB!={},	
			\[Alpha]\[Alpha] = Min[Transpose[BB][[2]]~Join~{\[Alpha]\[Alpha]}];
		];
(*Print["\[Alpha]=",\[Alpha]\[Alpha]];*)
		II = Select[Join[II,BB],#[[2]]==\[Alpha]\[Alpha]&];
(*Print["I=",II];*)
	];
]


FrobeniusEmbeddingDimensionMultiplicity[f_,i_,m_]:=Module[{a,lista,hijosAux,hijos,j,gen,frob,k},
	lista={};
	hijosAux={};
	If[f<m-1,Return[{}]];
	a = {{Table[j,{j,m,2m-1}],m-1}};
	If[f==m-1 && Length[a[[1,1]]]==i, AppendTo[lista,a]];
	hijos = Table[{quitaElementoMinimal[a[[1,1]],a[[1,1,j]]],a[[1,1,j]]},{j,2,Length[a[[1,1]]]}];
	While[True,
		For[j=1,j<=Length[hijos],j++,
			If[hijos[[j,2]]==f&&Length[hijos[[j,1]]]==i&&hijos[[j,1,1]]==m,AppendTo[lista,hijos[[j]]],
				If[hijos[[j,2]]<f,AppendTo[hijosAux,hijos[[j]]]];
			];
		];
		hijos = hijosAux;
		hijosAux={};
		If[hijos=={},Return[lista]];
		For[j=1,j<=Length[hijos],j++,
			gen = hijos[[j,1]];
			frob = hijos[[j,2]];
			For[k=1,k<=Length[gen],k++,
				If[gen[[k]]>frob&&gen[[k]]>m,AppendTo[hijosAux,{quitaElementoMinimal[gen,gen[[k]]],gen[[k]]}]];
			];
		];
		hijos = hijosAux;
		hijosAux={};
		If[hijos=={},Return[lista]];
	];
]


SonSameClass[smg_,f_,m_,e_]:=Module[{i,aux,sons={}},
	For[i=1,i<=Length[smg],i++,
		aux = quitaElementoMinimal[smg,smg[[i]]];
		If[FrobeniusNumber[aux]==f && Min[aux]==m && Length[aux]==e,
			AppendTo[sons,aux];
		];
	];
	Return@sons;
]


ComputeEquivalenceClass[S_]:=Module[{m,e,A,I,\[Alpha],C,frob,B,i,control=0},
	m = Min[S];
	e = Length[S];
	frob = FrobeniusNumber[S];
	A = {S};
	B ={S};
	While[True&&control<=10,
		C = {};
		For[i=1,i<=Length[B],i++,
			C = Join[C,SonSameClass[B[[i]],frob,m,e] ];
		];
		If[C=={},Return@A];
		A = Join[A,C];
		B = C;
control++;
	];
]


End[];
EndPackage[];
