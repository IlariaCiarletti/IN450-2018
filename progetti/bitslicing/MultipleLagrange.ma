DES1 = {{14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7}, {0,
15, 7, 4, 14, 2, 13, 10, 3, 6, 12, 11, 9, 5, 3, 8}, {4, 1, 14, 8,
13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0}, {15, 12, 8, 2, 4, 9, 1,
7, 5, 11, 3, 14, 10, 0, 6, 13}};
DES2 = {{15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10}, {3, 
    13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5}, {0, 14, 7, 11,
     10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15}, {13, 8, 10, 1, 3, 15, 4,
     2, 11, 6, 7, 12, 0, 5, 14, 9}};
DES3 = {{10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8}, {13, 
    7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1}, {13, 6, 4, 9, 
    8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7}, {1, 10, 13, 0, 6, 9, 8, 
    7, 4, 15, 14, 3, 11, 5, 2, 12}};
DES4 = {{7, 3, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15}, {13, 8,
     11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9}, {10, 6, 9, 0, 12,
     11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4}, {3, 15, 0, 6, 10, 1, 13, 8,
     9, 4, 5, 11, 12, 7, 2, 14}};
DES5 = {{2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9}, {14, 
    11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6}, {4, 2, 1, 11, 
    10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14}, {11, 8, 12, 7, 1, 14, 2,
     13, 6, 15, 0, 9, 10, 4, 5, 3}};
DES6 = {{12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11}, {10, 
    15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8}, {9, 14, 15, 5, 
    2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6}, {4, 3, 2, 12, 9, 5, 15, 
    10, 11, 14, 1, 7, 6, 0, 8, 13}};
DES7 = {{4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1}, {13, 
    0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6}, {1, 4, 11, 13, 
    12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2}, {6, 11, 13, 8, 1, 4, 10, 
    7, 9, 5, 0, 15, 14, 2, 3, 12}};
DES8 = {{13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7}, {1, 
    15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2}, {7, 11, 4, 1, 
    9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8}, {2, 1, 14, 7, 4, 10, 8, 
    13, 15, 12, 9, 0, 3, 5, 6, 11}};
Slice[sbox_, x_, bit_] :=
Mod[Floor[
sbox[[ (Mod[x, 2] + Mod[Floor[x/16], 2] 2) + 1,
If[Floor[x/2] >=16, Floor[x/2] - 16+1, Floor[x/2] + 1  ]]]/(2^
bit)], 2];

f=y^6+y+1;
len=Exponent[f,y];

FieldInversion[-1]=1;
FieldInversion[1]=1;
FieldInversion[k_] := FieldInversion[k] = Module[{u,v,g1,g2,i,ux,vx},
(
	u=PolynomialMod[k,2]; v=f; g1=1; g2=0;
	i=0;
	While[
		While[Coefficient[u,y,0]==0,
			(
				u=Simplify[u/y];
				If[Coefficient[g1,y,0]==0,
					g1=g1/y,
					g1=Simplify[PolynomialMod[(g1+f),{2}]/y]
				]
			)
		];
		(u=!=1)&&(i<10),
		(
			If[Exponent[u,y]<Exponent[v,y],
				(
					ux=v;v=u;u=ux;
					ux=g2;g2=g1;g1=ux
				)
			];
			u=PolynomialMod[(u+v),{2}];
			g1=PolynomialMod[(g1+g2),{2}];
			i++;
		)
	];
	g1
)];

Poly[n_]:=Reverse[IntegerDigits[n,2,6]].Table[y^i,{i,0,6-1}];

Int2Vec[x_]:=Reverse@IntegerDigits[x,2,len];
Int2Poly[x_]:=Int2Vec[x].Table[y^i,{i,0,len-1}];

Pol2Vec[x_]:=Reverse@CoefficientList[x,y,len];
Pol2Int[x_]:=FromDigits[Pol2Vec[x],2];

FP[a_,b_]:=FP[a,b]=Pol2Int[PolynomialMod[Int2Poly[a]Int2Poly[b],{f,2}]];
FA[a_,b_]:=FA[a,b]=Pol2Int[PolynomialMod[Int2Poly[a]+Int2Poly[b],{f,2}]];
FI[a_]:=FI[a]=Pol2Int[FieldInversion[Int2Poly[a]]];

rule1=GF[a_] GF[b_]:>GF[FP[a,b]];
rule2=GF[a_]+ GF[b_]:>GF[FA[a,b]];
rule3=Power[GF[a_],b_/;b>0]:>GF[Nest[FP[#,a]&,a,b-1]];
rule4=Power[GF[a_],-1]:>GF[FI[a]];
rule5=-GF[a_]:>GF[a];
rule6=(a_;IntegerQ[a]) GF[b_]:>GF[Nest[FA[#,b]&,a,a-1]];
rule7=GF[0]->0;
(*   
rule8 = 1\[Rule] GF[1];
rule9=b_ GF[a_]\[RuleDelayed] Mod[b,2] GF[a];
*)
rules={rule1,rule2,rule3,rule4,rule5,rule6,rule7};

(*Produttoria[k_]:=Partition[Map[(Collect[Expand[#],x]//.rules)&,x(Xp[[k]]-Drop[Xp,{k}])^(-1)-Drop[Xp,{k}] (Xp[[k]]-Drop[Xp,{k}])^(-1) ],2,2,{1,1},1];*)
Produttoria[k_]:=Partition[((x (Xp[[k]]-Drop[Xp,{k}])^(-1))//.rules)+(-Drop[Xp,{k}] (Xp[[k]]-Drop[Xp,{k}])^(-1)//.rules),2,2,{1,1},GF[1]];

f2[c_]:=PolynomialMod[Collect[Expand[c[[1]] c[[2]]],x]//.rules,2];
ApplyStep[p2_]:=If[(Length[p2]>=2),Partition[Map[f2,p2],2],f2[p2[[1]]],p2];

(* EXAMPLE RUN *)
Print[points=64];
Print[Xp=Map[GF,Range[points]-1];Length[Xp]];
Print[Yp=Map[GF,Table[Slice[DES1,i,1],{i,1,points}]];]
Print[Length[Yp]];

(* MAIN COMPUTATION of THE TABLE WITH PARTIAL RESULTS*)
sum=0;
XX=Table[
	{
	Produttoria[kk],
	Yp[[kk]],
	pp=Nest[ApplyStep,Produttoria[kk],Log[2,points]],
	tt=Yp[[kk]] pp,
	stt=f2[tt],
	sum=f2[{sum+ stt,1}]},{kk,1,points}
];

Print[TableForm[XX,TableDepth->2]];

lagrange=PolynomialMod[XX[[-1,-1]],{2}];

Print["Lagrange polynomial ",lagrange/.GF[a_]:>a];

(* VERIFICATION *)
legenda={"x_i","y_i","L(x_i)"};
Print[TableForm@Join[{legenda},Table[{Xp[[i]],PolynomialMod[PolynomialMod[(lagrange/.x->Xp[[i]])//.rules,{2}]//.rules,{2}],Yp[[i]]},{i,1,Length[Xp]}]]];

(* Calcolo i 6 polinomi: P7, P16, P20, P21, P25, P29 e il polinomio P1 *)

In[44]:= Print[
 Yp1 = Map[GF, Table[Slice[DES2, i, 2], {i, 0, points - 1}]]]

During evaluation of In[44]:= {GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0]}

In[74]:= sum = 0;
XX = Table[{Produttoria[kk], Yp1[[kk]], 
    pp = Nest[ApplyStep, Produttoria[kk], Log[2, points]], 
    tt = Yp1[[kk]] pp, stt = f2[tt], sum = f2[{sum + stt, 1}]}, {kk, 
    1, points}];
lagrange = PolynomialMod[XX[[-1, -1]], {2}];
Print["Lagrange polynomial ", lagrange];

During evaluation of In[74]:= Lagrange polynomial GF[1]+x^37 GF[2]+x^41 GF[3]+x^11 GF[4]+x^19 GF[5]+x^3 GF[6]+x^32 GF[6]+x^43 GF[6]+x^52 GF[8]+x^50 GF[9]+x^16 GF[11]+x^33 GF[11]+x^53 GF[11]+x^44 GF[12]+x^13 GF[13]+x^14 GF[14]+x^49 GF[14]+x^9 GF[15]+x^54 GF[15]+x^22 GF[16]+x^38 GF[17]+x^26 GF[18]+x^25 GF[19]+x GF[20]+x^6 GF[20]+x^23 GF[20]+x^18 GF[22]+x^45 GF[22]+x^28 GF[23]+x^35 GF[23]+x^27 GF[24]+x^36 GF[24]+x^7 GF[25]+x^56 GF[25]+x^8 GF[26]+x^48 GF[26]+x^58 GF[26]+x^2 GF[28]+x^12 GF[28]+x^46 GF[28]+x^4 GF[31]+x^24 GF[31]+x^29 GF[31]+x^40 GF[33]+x^20 GF[37]+x^10 GF[39]+x^51 GF[41]+x^60 GF[42]+x^5 GF[46]+x^17 GF[49]+x^39 GF[50]+x^57 GF[55]+x^15 GF[56]+x^21 GF[58]+x^42 GF[59]+x^34 GF[61]+x^30 GF[63]

In[45]:= P7[x_] := 
 GF[1] + x^37 GF[2] + x^41 GF[3] + x^11 GF[4] + x^19 GF[5] + 
  x^3 GF[6] + x^32 GF[6] + x^43 GF[6] + x^52 GF[8] + x^50 GF[9] + 
  x^16 GF[11] + x^33 GF[11] + x^53 GF[11] + x^44 GF[12] + 
  x^13 GF[13] + x^14 GF[14] + x^49 GF[14] + x^9 GF[15] + x^54 GF[15] +
   x^22 GF[16] + x^38 GF[17] + x^26 GF[18] + x^25 GF[19] + x GF[20] + 
  x^6 GF[20] + x^23 GF[20] + x^18 GF[22] + x^45 GF[22] + x^28 GF[23] +
   x^35 GF[23] + x^27 GF[24] + x^36 GF[24] + x^7 GF[25] + 
  x^56 GF[25] + x^8 GF[26] + x^48 GF[26] + x^58 GF[26] + x^2 GF[28] + 
  x^12 GF[28] + x^46 GF[28] + x^4 GF[31] + x^24 GF[31] + x^29 GF[31] +
   x^40 GF[33] + x^20 GF[37] + x^10 GF[39] + x^51 GF[41] + 
  x^60 GF[42] + x^5 GF[46] + x^17 GF[49] + x^39 GF[50] + x^57 GF[55] +
   x^15 GF[56] + x^21 GF[58] + x^42 GF[59] + x^34 GF[61] + x^30 GF[63]

In[46]:= Print[
 Yp2 = Map[GF, Table[Slice[DES4, i, 3], {i, 0, points - 1}]]]

During evaluation of In[46]:= {GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1]}

In[84]:= sum = 0;
XX = Table[{Produttoria[kk], Yp2[[kk]], 
    pp = Nest[ApplyStep, Produttoria[kk], Log[2, points]], 
    tt = Yp2[[kk]] pp, stt = f2[tt], sum = f2[{sum + stt, 1}]}, {kk, 
    1, points}];
lagrange = PolynomialMod[XX[[-1, -1]], {2}];
Print["Lagrange polynomial ", lagrange];

During evaluation of In[84]:= Lagrange polynomial x^27 GF[1]+x^45 GF[1]+x^54 GF[1]+x^34 GF[2]+x^6 GF[3]+x^5 GF[4]+x^12 GF[5]+x^39 GF[7]+x^3 GF[8]+x^17 GF[9]+x^51 GF[10]+x^20 GF[12]+x^48 GF[13]+x^14 GF[15]+x^18 GF[15]+x^49 GF[15]+x^10 GF[16]+x^24 GF[17]+x^33 GF[18]+x^40 GF[19]+x^15 GF[21]+x^28 GF[22]+x^35 GF[22]+x^36 GF[22]+x^7 GF[24]+x^9 GF[24]+x^56 GF[24]+x^57 GF[27]+x^30 GF[29]+x^60 GF[30]+x^41 GF[40]+x^4 GF[41]+x^11 GF[41]+x^43 GF[41]+x GF[42]+x^50 GF[42]+x^58 GF[42]+x^26 GF[43]+x^8 GF[50]+x^22 GF[50]+x^23 GF[50]+x^19 GF[51]+x^52 GF[54]+x^2 GF[55]+x^37 GF[55]+x^53 GF[55]+x^16 GF[56]+x^44 GF[56]+x^46 GF[56]+x^38 GF[57]+x^21 GF[58]+x^42 GF[59]+x^13 GF[62]+x^25 GF[63]+x^29 GF[63]+x^32 GF[63]

In[47]:= P16[x_] :=  
 x^27 GF[1] + x^45 GF[1] + x^54 GF[1] + x^34 GF[2] + x^6 GF[3] + 
  x^5 GF[4] + x^12 GF[5] + x^39 GF[7] + x^3 GF[8] + x^17 GF[9] + 
  x^51 GF[10] + x^20 GF[12] + x^48 GF[13] + x^14 GF[15] + 
  x^18 GF[15] + x^49 GF[15] + x^10 GF[16] + x^24 GF[17] + 
  x^33 GF[18] + x^40 GF[19] + x^15 GF[21] + x^28 GF[22] + 
  x^35 GF[22] + x^36 GF[22] + x^7 GF[24] + x^9 GF[24] + x^56 GF[24] + 
  x^57 GF[27] + x^30 GF[29] + x^60 GF[30] + x^41 GF[40] + x^4 GF[41] +
   x^11 GF[41] + x^43 GF[41] + x GF[42] + x^50 GF[42] + x^58 GF[42] + 
  x^26 GF[43] + x^8 GF[50] + x^22 GF[50] + x^23 GF[50] + x^19 GF[51] +
   x^52 GF[54] + x^2 GF[55] + x^37 GF[55] + x^53 GF[55] + 
  x^16 GF[56] + x^44 GF[56] + x^46 GF[56] + x^38 GF[57] + 
  x^21 GF[58] + x^42 GF[59] + x^13 GF[62] + x^25 GF[63] + 
  x^29 GF[63] + x^32 GF[63]

In[48]:= Print[
 Yp3 = Map[GF, Table[Slice[DES5, i, 3], {i, 0, points - 1}]]]

During evaluation of In[48]:= {GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[0]}

In[90]:= sum = 0;
XX = Table[{Produttoria[kk], Yp3[[kk]], 
    pp = Nest[ApplyStep, Produttoria[kk], Log[2, points]], 
    tt = Yp3[[kk]] pp, stt = f2[tt], sum = f2[{sum + stt, 1}]}, {kk, 
    1, points}];
lagrange = PolynomialMod[XX[[-1, -1]], {2}];
Print["Lagrange polynomial ", lagrange];

During evaluation of In[90]:= Lagrange polynomial x^27 GF[1]+x^45 GF[1]+x^54 GF[1]+x^56 GF[3]+x^49 GF[5]+x^16 GF[6]+x^37 GF[7]+x^28 GF[8]+x^50 GF[10]+x^8 GF[11]+x^7 GF[13]+x^13 GF[14]+x^41 GF[14]+x^18 GF[15]+x^35 GF[17]+x^14 GF[18]+x^32 GF[20]+x^11 GF[21]+x^36 GF[22]+x^19 GF[23]+x^26 GF[23]+x^9 GF[24]+x^38 GF[25]+x^52 GF[25]+x^4 GF[26]+x^25 GF[27]+x GF[28]+x^22 GF[29]+x^44 GF[30]+x^2 GF[31]+x^33 GF[33]+x^51 GF[33]+x^48 GF[37]+x^57 GF[37]+x^24 GF[39]+x^60 GF[39]+x^46 GF[40]+x^20 GF[41]+x^5 GF[42]+x^43 GF[43]+x^12 GF[46]+x^30 GF[46]+x^3 GF[49]+x^39 GF[49]+x^40 GF[50]+x^29 GF[51]+x^23 GF[54]+x^10 GF[55]+x^17 GF[56]+x^58 GF[57]+x^21 GF[58]+x^42 GF[59]+x^6 GF[61]+x^15 GF[61]+x^53 GF[62]+x^34 GF[63]

In[49]:= P20[x_] := 
 x^27 GF[1] + x^45 GF[1] + x^54 GF[1] + x^56 GF[3] + x^49 GF[5] + 
  x^16 GF[6] + x^37 GF[7] + x^28 GF[8] + x^50 GF[10] + x^8 GF[11] + 
  x^7 GF[13] + x^13 GF[14] + x^41 GF[14] + x^18 GF[15] + x^35 GF[17] +
   x^14 GF[18] + x^32 GF[20] + x^11 GF[21] + x^36 GF[22] + 
  x^19 GF[23] + x^26 GF[23] + x^9 GF[24] + x^38 GF[25] + x^52 GF[25] +
   x^4 GF[26] + x^25 GF[27] + x GF[28] + x^22 GF[29] + x^44 GF[30] + 
  x^2 GF[31] + x^33 GF[33] + x^51 GF[33] + x^48 GF[37] + x^57 GF[37] +
   x^24 GF[39] + x^60 GF[39] + x^46 GF[40] + x^20 GF[41] + 
  x^5 GF[42] + x^43 GF[43] + x^12 GF[46] + x^30 GF[46] + x^3 GF[49] + 
  x^39 GF[49] + x^40 GF[50] + x^29 GF[51] + x^23 GF[54] + 
  x^10 GF[55] + x^17 GF[56] + x^58 GF[57] + x^21 GF[58] + 
  x^42 GF[59] + x^6 GF[61] + x^15 GF[61] + x^53 GF[62] + x^34 GF[63]

In[95]:= Print[
 Yp4 = Map[GF, Table[Slice[DES6, i, 0], {i, 0, points - 1}]]]

During evaluation of In[95]:= {GF[0],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[1],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[1],GF[0],GF[1],GF[0],GF[0],GF[1]}

In[96]:= sum = 0;
XX = Table[{Produttoria[kk], Yp4[[kk]], 
    pp = Nest[ApplyStep, Produttoria[kk], Log[2, points]], 
    tt = Yp4[[kk]] pp, stt = f2[tt], sum = f2[{sum + stt, 1}]}, {kk, 
    1, points}];
lagrange = PolynomialMod[XX[[-1, -1]], {2}];
Print["Lagrange polynomial ", lagrange];

During evaluation of In[96]:= Lagrange polynomial x^7 GF[1]+x^14 GF[1]+x^28 GF[1]+x^35 GF[1]+x^49 GF[1]+x^56 GF[1]+x^15 GF[2]+x^41 GF[3]+x^30 GF[4]+x^19 GF[5]+x^52 GF[8]+x^39 GF[9]+x^57 GF[12]+x^13 GF[13]+x^18 GF[14]+x^54 GF[15]+x^60 GF[16]+x^38 GF[17]+x^26 GF[18]+x^51 GF[19]+x^45 GF[22]+x^36 GF[23]+x^27 GF[24]+x^9 GF[25]+x^17 GF[32]+x^62 GF[32]+x^6 GF[33]+x^16 GF[33]+x^31 GF[36]+x^40 GF[36]+x^3 GF[37]+x^8 GF[37]+x^20 GF[38]+x^47 GF[38]+x^4 GF[39]+x^33 GF[39]+x^23 GF[40]+x^11 GF[41]+x^50 GF[42]+x^53 GF[43]+x^2 GF[46]+x^48 GF[46]+x^10 GF[47]+x^55 GF[47]+x^34 GF[48]+x^61 GF[48]+x^12 GF[49]+x^32 GF[49]+x^22 GF[50]+x^46 GF[51]+x^43 GF[54]+x^37 GF[55]+x^44 GF[56]+x^29 GF[57]+x^42 GF[58]+x^21 GF[59]+x^5 GF[60]+x^59 GF[60]+x GF[61]+x^24 GF[61]+x^58 GF[62]+x^25 GF[63]

In[50]:= P21[x_] :=  
 x^7 GF[1] + x^14 GF[1] + x^28 GF[1] + x^35 GF[1] + x^49 GF[1] + 
  x^56 GF[1] + x^15 GF[2] + x^41 GF[3] + x^30 GF[4] + x^19 GF[5] + 
  x^52 GF[8] + x^39 GF[9] + x^57 GF[12] + x^13 GF[13] + x^18 GF[14] + 
  x^54 GF[15] + x^60 GF[16] + x^38 GF[17] + x^26 GF[18] + 
  x^51 GF[19] + x^45 GF[22] + x^36 GF[23] + x^27 GF[24] + x^9 GF[25] +
   x^17 GF[32] + x^62 GF[32] + x^6 GF[33] + x^16 GF[33] + 
  x^31 GF[36] + x^40 GF[36] + x^3 GF[37] + x^8 GF[37] + x^20 GF[38] + 
  x^47 GF[38] + x^4 GF[39] + x^33 GF[39] + x^23 GF[40] + x^11 GF[41] +
   x^50 GF[42] + x^53 GF[43] + x^2 GF[46] + x^48 GF[46] + 
  x^10 GF[47] + x^55 GF[47] + x^34 GF[48] + x^61 GF[48] + 
  x^12 GF[49] + x^32 GF[49] + x^22 GF[50] + x^46 GF[51] + 
  x^43 GF[54] + x^37 GF[55] + x^44 GF[56] + x^29 GF[57] + 
  x^42 GF[58] + x^21 GF[59] + x^5 GF[60] + x^59 GF[60] + x GF[61] + 
  x^24 GF[61] + x^58 GF[62] + x^25 GF[63]

In[51]:= Print[
 Yp5 = Map[GF, Table[Slice[DES7, i, 0], {i, 0, points - 1}]]]

During evaluation of In[51]:= {GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0]}

In[101]:= sum = 0;
XX = Table[{Produttoria[kk], Yp5[[kk]], 
    pp = Nest[ApplyStep, Produttoria[kk], Log[2, points]], 
    tt = Yp5[[kk]] pp, stt = f2[tt], sum = f2[{sum + stt, 1}]}, {kk, 
    1, points}];
lagrange = PolynomialMod[XX[[-1, -1]], {2}];
Print["Lagrange polynomial ", lagrange];

During evaluation of In[101]:= Lagrange polynomial x^11 GF[2]+x^10 GF[3]+x^51 GF[3]+x^22 GF[4]+x^20 GF[5]+x^39 GF[5]+x^5 GF[8]+x^57 GF[8]+x^37 GF[9]+x^25 GF[12]+x^17 GF[13]+x^30 GF[13]+x^45 GF[14]+x^36 GF[15]+x^44 GF[16]+x^15 GF[17]+x^40 GF[17]+x^34 GF[18]+x^60 GF[18]+x^50 GF[19]+x^9 GF[22]+x^27 GF[23]+x^18 GF[24]+x^54 GF[25]+x^53 GF[32]+x^62 GF[32]+x^2 GF[33]+x^3 GF[33]+x^52 GF[34]+x^38 GF[35]+x^31 GF[36]+x^58 GF[36]+x GF[37]+x^33 GF[37]+x^29 GF[38]+x^47 GF[38]+x^32 GF[39]+x^48 GF[39]+x^19 GF[44]+x^26 GF[45]+x^16 GF[46]+x^24 GF[46]+x^46 GF[47]+x^55 GF[47]+x^43 GF[48]+x^61 GF[48]+x^4 GF[49]+x^6 GF[49]+x^41 GF[52]+x^13 GF[53]+x^7 GF[58]+x^28 GF[58]+x^49 GF[58]+x^14 GF[59]+x^35 GF[59]+x^56 GF[59]+x^23 GF[60]+x^59 GF[60]+x^8 GF[61]+x^12 GF[61]

In[52]:= P25[x_] := 
 x^11 GF[2] + x^10 GF[3] + x^51 GF[3] + x^22 GF[4] + x^20 GF[5] + 
  x^39 GF[5] + x^5 GF[8] + x^57 GF[8] + x^37 GF[9] + x^25 GF[12] + 
  x^17 GF[13] + x^30 GF[13] + x^45 GF[14] + x^36 GF[15] + 
  x^44 GF[16] + x^15 GF[17] + x^40 GF[17] + x^34 GF[18] + 
  x^60 GF[18] + x^50 GF[19] + x^9 GF[22] + x^27 GF[23] + x^18 GF[24] +
   x^54 GF[25] + x^53 GF[32] + x^62 GF[32] + x^2 GF[33] + x^3 GF[33] +
   x^52 GF[34] + x^38 GF[35] + x^31 GF[36] + x^58 GF[36] + x GF[37] + 
  x^33 GF[37] + x^29 GF[38] + x^47 GF[38] + x^32 GF[39] + 
  x^48 GF[39] + x^19 GF[44] + x^26 GF[45] + x^16 GF[46] + 
  x^24 GF[46] + x^46 GF[47] + x^55 GF[47] + x^43 GF[48] + 
  x^61 GF[48] + x^4 GF[49] + x^6 GF[49] + x^41 GF[52] + x^13 GF[53] + 
  x^7 GF[58] + x^28 GF[58] + x^49 GF[58] + x^14 GF[59] + x^35 GF[59] +
   x^56 GF[59] + x^23 GF[60] + x^59 GF[60] + x^8 GF[61] + x^12 GF[61]

In[105]:= Print[
 Yp6 = Map[GF, Table[Slice[DES8, i, 0], {i, 0, points - 1}]]]

During evaluation of In[105]:= {GF[1],GF[1],GF[0],GF[1],GF[0],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1],GF[1],GF[1],GF[0],GF[1],GF[0],GF[1],GF[0],GF[0],GF[0],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1],GF[0],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[1]}

In[106]:= sum = 0;
XX = Table[{Produttoria[kk], Yp6[[kk]], 
    pp = Nest[ApplyStep, Produttoria[kk], Log[2, points]], 
    tt = Yp6[[kk]] pp, stt = f2[tt], sum = f2[{sum + stt, 1}]}, {kk, 
    1, points}];
lagrange = PolynomialMod[XX[[-1, -1]], {2}];
Print["Lagrange polynomial ", lagrange];

During evaluation of In[106]:= Lagrange polynomial GF[1]+x^11 GF[1]+x^22 GF[1]+x^25 GF[1]+x^37 GF[1]+x^44 GF[1]+x^50 GF[1]+x^20 GF[2]+x^40 GF[4]+x^33 GF[7]+x^10 GF[9]+x^48 GF[10]+x^34 GF[12]+x^18 GF[14]+x^54 GF[14]+x^17 GF[16]+x^5 GF[19]+x^3 GF[21]+x^36 GF[23]+x^45 GF[23]+x^9 GF[25]+x^27 GF[25]+x^24 GF[27]+x^6 GF[29]+x^12 GF[30]+x^4 GF[33]+x^19 GF[33]+x^53 GF[33]+x^56 GF[33]+x^2 GF[37]+x^28 GF[37]+x^41 GF[37]+x^58 GF[37]+x GF[39]+x^14 GF[39]+x^29 GF[39]+x^52 GF[39]+x^57 GF[41]+x^30 GF[42]+x^7 GF[46]+x^26 GF[46]+x^32 GF[46]+x^46 GF[46]+x^8 GF[49]+x^38 GF[49]+x^43 GF[49]+x^49 GF[49]+x^51 GF[50]+x^60 GF[55]+x^39 GF[56]+x^42 GF[58]+x^21 GF[59]+x^13 GF[61]+x^16 GF[61]+x^23 GF[61]+x^35 GF[61]+x^15 GF[63]

In[53]:= P29[x_] := 
 GF[1] + x^11 GF[1] + x^22 GF[1] + x^25 GF[1] + x^37 GF[1] + 
  x^44 GF[1] + x^50 GF[1] + x^20 GF[2] + x^40 GF[4] + x^33 GF[7] + 
  x^10 GF[9] + x^48 GF[10] + x^34 GF[12] + x^18 GF[14] + x^54 GF[14] +
   x^17 GF[16] + x^5 GF[19] + x^3 GF[21] + x^36 GF[23] + x^45 GF[23] +
   x^9 GF[25] + x^27 GF[25] + x^24 GF[27] + x^6 GF[29] + x^12 GF[30] +
   x^4 GF[33] + x^19 GF[33] + x^53 GF[33] + x^56 GF[33] + x^2 GF[37] +
   x^28 GF[37] + x^41 GF[37] + x^58 GF[37] + x GF[39] + x^14 GF[39] + 
  x^29 GF[39] + x^52 GF[39] + x^57 GF[41] + x^30 GF[42] + x^7 GF[46] +
   x^26 GF[46] + x^32 GF[46] + x^46 GF[46] + x^8 GF[49] + 
  x^38 GF[49] + x^43 GF[49] + x^49 GF[49] + x^51 GF[50] + 
  x^60 GF[55] + x^39 GF[56] + x^42 GF[58] + x^21 GF[59] + 
  x^13 GF[61] + x^16 GF[61] + x^23 GF[61] + x^35 GF[61] + x^15 GF[63]

In[54]:= Print[
 Yp = Map[GF, Table[Slice[DES1, i, 0], {i, 0, points - 1}]]]

During evaluation of In[54]:= {GF[0],GF[0],GF[0],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[1],GF[1],GF[1],GF[0],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1],GF[0],GF[0],GF[0],GF[1],GF[1],GF[1],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[1],GF[1],GF[0],GF[0],GF[1],GF[1],GF[0],GF[1],GF[1],GF[1],GF[1],GF[0],GF[1],GF[0],GF[0],GF[0],GF[1],GF[0],GF[0],GF[1]}

In[122]:= sum = 0;
XX = Table[{Produttoria[kk], Yp[[kk]], 
    pp = Nest[ApplyStep, Produttoria[kk], Log[2, points]], 
    tt = Yp[[kk]] pp, stt = f2[tt], sum = f2[{sum + stt, 1}]}, {kk, 1,
     points}];
lagrange = PolynomialMod[XX[[-1, -1]], {2}];
Print["Lagrange polynomial ", lagrange];

During evaluation of In[122]:= Lagrange polynomial x^21 GF[1]+x^42 GF[1]+x^28 GF[6]+x^37 GF[6]+x^24 GF[7]+x^12 GF[10]+x^14 GF[11]+x^50 GF[11]+x^39 GF[14]+x^54 GF[14]+x^60 GF[14]+x^11 GF[20]+x^56 GF[20]+x^48 GF[21]+x^15 GF[23]+x^45 GF[23]+x^57 GF[23]+x^27 GF[25]+x^30 GF[25]+x^51 GF[25]+x^7 GF[26]+x^25 GF[26]+x^6 GF[27]+x^22 GF[28]+x^49 GF[28]+x^33 GF[29]+x^3 GF[30]+x^35 GF[31]+x^44 GF[31]+x^8 GF[40]+x^20 GF[40]+x^26 GF[40]+x^53 GF[40]+x^2 GF[43]+x^5 GF[43]+x^29 GF[43]+x^38 GF[43]+x^16 GF[51]+x^40 GF[51]+x^43 GF[51]+x^52 GF[51]+x^4 GF[54]+x^10 GF[54]+x^13 GF[54]+x^58 GF[54]+x^17 GF[57]+x^23 GF[57]+x^32 GF[57]+x^41 GF[57]+x GF[62]+x^19 GF[62]+x^34 GF[62]+x^46 GF[62]

In[55]:= P1[x_] := 
 x^21 GF[1] + x^42 GF[1] + x^28 GF[6] + x^37 GF[6] + x^24 GF[7] + 
  x^12 GF[10] + x^14 GF[11] + x^50 GF[11] + x^39 GF[14] + 
  x^54 GF[14] + x^60 GF[14] + x^11 GF[20] + x^56 GF[20] + 
  x^48 GF[21] + x^15 GF[23] + x^45 GF[23] + x^57 GF[23] + 
  x^27 GF[25] + x^30 GF[25] + x^51 GF[25] + x^7 GF[26] + x^25 GF[26] +
   x^6 GF[27] + x^22 GF[28] + x^49 GF[28] + x^33 GF[29] + x^3 GF[30] +
   x^35 GF[31] + x^44 GF[31] + x^8 GF[40] + x^20 GF[40] + 
  x^26 GF[40] + x^53 GF[40] + x^2 GF[43] + x^5 GF[43] + x^29 GF[43] + 
  x^38 GF[43] + x^16 GF[51] + x^40 GF[51] + x^43 GF[51] + 
  x^52 GF[51] + x^4 GF[54] + x^10 GF[54] + x^13 GF[54] + x^58 GF[54] +
   x^17 GF[57] + x^23 GF[57] + x^32 GF[57] + x^41 GF[57] + x GF[62] + 
  x^19 GF[62] + x^34 GF[62] + x^46 GF[62]

(*Combinazione primo e terzo round *)

In[92]:= f3[a_[x_], b_] := 
  PolynomialMod[Collect[Expand[a[x] b], x] //. rules, 2];

In[98]:= P[x1_, x2_, x3_, x4_, x5_, x6_, x7_, x8_] := 
  P1[f3[P25[x7], GF[32]] + f3[P16[x4], GF[16]] + f3[P7[x2], GF[8]] + 
     f3[P20[x5], GF[4]] + f3[P21[x6], GF[2]] + P29[x8] //. rules];

In[76]:= PolynomialMod[Collect[Expand[P25[x] GF[32]], x] //. rules, 2]

Out[76]= x^8 GF[2] + x^12 GF[2] + x^11 GF[3] + x^22 GF[6] + 
 x^14 GF[7] + x^35 GF[7] + x^56 GF[7] + x^4 GF[8] + x^6 GF[8] + 
 x^45 GF[9] + x^25 GF[10] + x^5 GF[12] + x^57 GF[12] + x^13 GF[14] + 
 x^2 GF[16] + x^3 GF[16] + x^38 GF[19] + x^18 GF[20] + x^32 GF[21] + 
 x^48 GF[21] + x GF[22] + x^33 GF[22] + x^44 GF[24] + x^46 GF[25] + 
 x^55 GF[25] + x^26 GF[26] + x^34 GF[27] + x^60 GF[27] + x^9 GF[29] + 
 x^23 GF[34] + x^59 GF[34] + x^10 GF[35] + x^51 GF[35] + x^20 GF[38] +
  x^39 GF[38] + x^7 GF[39] + x^28 GF[39] + x^49 GF[39] + x^43 GF[40] +
  x^61 GF[40] + x^36 GF[41] + x^17 GF[42] + x^30 GF[42] + 
 x^37 GF[44] + x^41 GF[46] + x^53 GF[48] + x^62 GF[48] + x^52 GF[51] +
  x^54 GF[52] + x^29 GF[53] + x^47 GF[53] + x^31 GF[54] + 
 x^58 GF[54] + x^15 GF[56] + x^40 GF[56] + x^16 GF[57] + x^24 GF[57] +
  x^19 GF[58] + x^50 GF[59] + x^27 GF[61]

In[95]:= f3[P25[x7], GF[32]] + f3[P16[x4], GF[16]]

Out[95]= x4^38 GF[2] + x7^8 GF[2] + x7^12 GF[2] + x4^5 GF[3] + 
 x7^11 GF[3] + x4^20 GF[5] + x4^3 GF[6] + x7^22 GF[6] + x7^14 GF[7] + 
 x7^35 GF[7] + x7^56 GF[7] + x7^4 GF[8] + x7^6 GF[8] + x7^45 GF[9] + 
 x4^7 GF[10] + x4^9 GF[10] + x4^56 GF[10] + x7^25 GF[10] + 
 x4^10 GF[12] + x7^5 GF[12] + x7^57 GF[12] + x4^4 GF[14] + 
 x4^11 GF[14] + x4^43 GF[14] + x7^13 GF[14] + x4^27 GF[16] + 
 x4^45 GF[16] + x4^54 GF[16] + x7^2 GF[16] + x7^3 GF[16] + 
 x4^16 GF[18] + x4^44 GF[18] + x4^46 GF[18] + x4^12 GF[19] + 
 x7^38 GF[19] + x7^18 GF[20] + x4^48 GF[21] + x7^32 GF[21] + 
 x7^48 GF[21] + x4^17 GF[22] + x7 GF[22] + x7^33 GF[22] + 
 x7^44 GF[24] + x4^30 GF[25] + x7^46 GF[25] + x7^55 GF[25] + 
 x7^26 GF[26] + x7^34 GF[27] + x7^60 GF[27] + x4^24 GF[28] + 
 x7^9 GF[29] + x4^41 GF[30] + x4^15 GF[31] + x4^34 GF[32] + 
 x4^25 GF[33] + x4^29 GF[33] + x4^32 GF[33] + x4^42 GF[34] + 
 x7^23 GF[34] + x7^59 GF[34] + x7^10 GF[35] + x7^51 GF[35] + 
 x4^19 GF[36] + x4^51 GF[38] + x7^20 GF[38] + x7^39 GF[38] + 
 x4^2 GF[39] + x4^37 GF[39] + x4^53 GF[39] + x7^7 GF[39] + 
 x7^28 GF[39] + x7^49 GF[39] + x7^43 GF[40] + x7^61 GF[40] + 
 x4^60 GF[41] + x7^36 GF[41] + x7^17 GF[42] + x7^30 GF[42] + 
 x4^33 GF[44] + x7^37 GF[44] + x4^26 GF[46] + x7^41 GF[46] + 
 x4^28 GF[47] + x4^35 GF[47] + x4^36 GF[47] + x4^6 GF[48] + 
 x7^53 GF[48] + x7^62 GF[48] + x4^13 GF[49] + x4^21 GF[50] + 
 x4^39 GF[51] + x7^52 GF[51] + x4^8 GF[52] + x4^22 GF[52] + 
 x4^23 GF[52] + x7^54 GF[52] + x4^14 GF[53] + x4^18 GF[53] + 
 x4^49 GF[53] + x7^29 GF[53] + x7^47 GF[53] + x7^31 GF[54] + 
 x7^58 GF[54] + x4^52 GF[55] + x7^15 GF[56] + x7^40 GF[56] + 
 x7^16 GF[57] + x7^24 GF[57] + x4^57 GF[58] + x7^19 GF[58] + 
 x7^50 GF[59] + x4^40 GF[60] + x7^27 GF[61] + x4 GF[62] + 
 x4^50 GF[62] + x4^58 GF[62]


In[103]:= Expand[
 GF[62] (X5^3 GF[1] + X5^39 GF[1] + X6^6 GF[1] + X6^16 GF[1] + 
     X8^11 GF[1]) /. rules]

Out[103]= 
X5^3 GF[1] GF[62] + X5^39 GF[1] GF[62] + X6^6 GF[1] GF[62] + 
 X6^16 GF[1] GF[62] + X8^11 GF[1] GF[62]
In[105]:= Expand[P[X1, X2, X3, X4, X5, X6, X7, X8]] /. GF[a]:>a

