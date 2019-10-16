/// Hyperelliptic Parametrizations of $\Q$-curves
/// 


/* Cases done: 
N=85, 93, 106, 115, 122, 129, 154, 158, 161, 165, 170, 186, 209, 215, 230, 285, 286,  357, 390

Cases non possible 




*/


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
//Previous Functions: 
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////


/*
Given an element d of a A<theta>, 
contruscts the corresponding TwoCovering 
of the hyperelliptic curve y^2=f(x), 
together with the map to P^1 giving the 
"x-coordinate"
*/


function TwoCoveringQ(d)
A<theta>:=Parent(d);
f<x>:=Modulus(A);
n:=Degree(f);
PA:=PolynomialRing(A,n);
g:=d*(&+[PA.i*theta^(i-1): i in [1..n]])^2;
Cg,Mg:=CoefficientsAndMonomials(g);
F:=BaseField(A);
PF:=PolynomialRing(F,n);
Q:=[0*PF.1: j in [1..n]];
for i in [1..#Cg] do
EC:=[j*Monomial(PF,Exponents(Mg[i])): j in ElementToSequence(Cg[i])];
for j in [1..#EC] do Q[j]:=Q[j]+EC[j]; end for;
end for; 
CQ:=Curve(ProjectiveSpace(PF),Q[3..n]);
mCQ:=map<CQ->ProjectiveSpace(F,1)|[-Q[1],Q[2]]>;
return CQ,mCQ;
end function;



//The following function computes for a given hyperelliptic curve X
//All the "deltas" corresponding to points of the twists of 2-covers of X
//in the form point-theta if the point is not Weierstrass point
//and 1 if the point is at infinity (if the point is Weierstrass 
// returns the answer of TwoCoverDescent of Bruin-Stoll).
//It also prints the deltas not corresponding to points. 
//it returns a boolean that is true if all deltas are productive
//and a list of all the productive deltas. 


function MyDeltas(X,uXrat);
P1:=Scheme(Setseq(uXrat)[1]);
uX:=map<X->P1|[X.1,X.3]>;
Hk,AtoHk:=TwoCoverDescent(X);
A<theta>:=Domain(AtoHk);
deltas:=[h@@AtoHk : h in Hk];
b:=true;
deltasp:=[];
if 1 in deltas then deltasp:=[A!1]; Remove(~deltas,1); end if;
for d in deltas do 
C,mC:=TwoCoveringQ(d);
Ptw:={pt: pt in uXrat | #Points((Codomain(mC)![pt[1],pt[2]])@@mC) gt 0};
if #Ptw eq 0 then print "Delta=",d," is not productive "; b:=false; 
else PtnW:=[pt: pt in Ptw | #Points((Codomain(uX)![pt[1],pt[2]])@@uX) gt 1];
if #PtnW eq 0 then Append(~deltasp,d); 
elif PtnW[1][2] eq 0 then Append(~deltasp,A!1);
else 
Append(~deltasp,PtnW[1][1]/PtnW[1][2]-theta); 
end if;
end if;
end for;
return b,deltasp; 
end function; 


//We collect in a function the final application of Elliptic Chabauty
//We pass a degree 4 polynomial over a number field K
//a list of deltas (elements of A=K[x]/(f) )
//a set of (K-)rational points of P1 whose preimage by C->P1 is K-rational
//where C is the hyperelliptic curve given by y^2=f(x)
//and the map is the "x-map"
//It answers the set of twists done (not very useful)
//and the rational points obtained 
//The parameter IndexBound allows to put some more primes for Chabauty
//with larger primes, more easy Chabauty succeds, but longer to show saturation


function MyEllipticChabauty(g,deltas,uXrat: IndexBound:=2*3*5)
P1:=Scheme(Setseq(uXrat)[1]);
A:=Parent(deltas[1]);
K:=BaseRing(g);
twistsb:=[];
pointsdone:={};
L<Th>:=quo<PolynomialRing(K)| g>; AtoL:=hom<A->L|Th>;
twist_list:=[Norm(AtoL(delta)):delta in deltas];
//The following computes the real list of twists (with the points they produce)
twists:=[];twistspt:=[];
PointsCover:={};
for tw in twist_list do 
H:=HyperellipticCurve(tw*g);
Ptw:={pt: pt in uXrat | pt[2] ne 0 and #Points(H,pt[1]/pt[2]) gt 0};
if #PointsAtInfinity(H) gt 0 then Ptw:=Ptw join {pt: pt in uXrat| pt[2] eq 0};end if;ª
if #(Ptw meet PointsCover) ne #Ptw then Append(~twists,tw); 
PointsCover:=PointsCover join Ptw; Append(~twistspt,Ptw);
end if;
end for;
print(twists);
print(twistspt);
for i in [1..#twists] do
tw:=twists[i];
H:=HyperellipticCurve(tw*g);
P0:=Setseq(PointsAtInfinity(H)) cat Setseq(&join{Points(H,pt[1]/pt[2]) : pt in twistspt[i]| pt[2] ne 0});
p0:=P0[1]; 
E,HtoE:=EllipticCurve(H,p0);
Em,EtoEm:=IntegralModel(E);
if tw eq 1 then Em:=E; EtoEm:=Isomorphism(E,E); end if;
rank, gs:=DescentInformation(Em: RankOnly:=true);
print"Rank for twist=",i,"=",rank;
if rank[1] lt Degree(K) then 
TEm,mTEm:=TorsionSubgroup(Em);
HtoP1:=map<H->P1|[H.1,H.3]>;
EmtoP1:=Inverse(EtoEm)*Inverse(HtoE)*HtoP1; 
u := Extend(EmtoP1);
if rank[1] eq 0 then V:=TEm; mwmap:=mTEm; 
b:=true;
else 
ABB,AB:=AbelianBasis(TEm);
G:=AbelianGroup(AB cat [0: i in [1..rank[1]]]);
G;
gs:=[mTEm(a): a in ABB] cat gs;
gs:=Saturation(gs, 6);
gs;
mwmap:=map<G->Em|a:->&+[a[i]*gs[i]:i in [1..#gs]]where a:=Eltseq(a)>;
//SetVerbose("EllChab", 1);
V,R:=Chabauty(mwmap,u:IndexBound:=IndexBound); 
print "supp(R) =", PrimeDivisors(R);
b:=&and[IsPSaturated(mwmap,p) : p in PrimeDivisors(R)]; 
print "Verify Saturation=",  b; 
end if;
pttw:={EvaluateByPowerSeries(u,mwmap(P)):P in V};
pttw:={pt: pt in pttw | pt in P1(Rationals())};
if b then Append(~twistsb,tw); pointsdone:=pointsdone join pttw;
print "Solutions for twist ",i," = ",pttw;
end if;
end if;
end for;
return twistsb,pointsdone;
end function;









////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////





//N=85
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);

f:=(x^2 - 2*x + 5)*(x^4 - 2*x^3 + 3*x^2 - 6*x + 5);
X:=HyperellipticCurve(f);
Ff:=Factorization(f);
Ff;
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

b,deltas:=MyDeltas(X,uXrat);

print "Productive deltas =", deltas; 
/*
Productive deltas =[
    1,
    -theta + 2,
    -theta + 3/2,
    -theta - 4/3,
    -theta
]
*/

//We try first the factorization at Q.

g:=Ff[2][1];g;

MyEllipticChabauty(g,deltas,uXrat);

/*
[ 1, 5, 17/16, 2125/81 ]
[
    { (1 : 1), (1 : 0) },
    { (2 : 1), (0 : 1) },
    { (3/2 : 1) },
    { (-4/3 : 1) }
]

Torsion Subgroup = Z/4
Analytic rank = 0
     ==> Rank(E) = 0

Rank for twist= 1 = [ 0, 0 ]
Solutions for twist  1  =  { (1 : 1), (1 : 0) }

Torsion Subgroup = Z/2
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 2 = [ 1, 1 ]

Torsion Subgroup = Z/4
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 3 = [ 1, 1 ]

Torsion Subgroup = Z/2
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 4 = [ 1, 1 ]
[ 1 ]
{ (1 : 1), (1 : 0) }

*/

//The first delta succeds 

//So they remain only 4 deltas
Exclude(~deltas,1);

//We go to the extension adjoining one root of the degree 2 factor


K<alpha>:=NumberField((x^2 - 2*x + 5));
fac:=Factorization(ChangeRing(f,K));
fac;


//We get a factorization also of the second factor.
g:=fac[1][1]*fac[2][1]*fac[3][1];
g;


MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1/16*(-34*alpha + 17),
    5*alpha - 10,
    1/81*(1785*alpha - 170)
]
[
    { (3/2 : 1) },
    { (2 : 1), (0 : 1) },
    { (-4/3 : 1) }
]

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = -561816*alpha - 4026348)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-4681800*alpha + 11704500 : 16236482400*alpha - 16236482400 : 1),
(-561816*alpha - 4026348 : 7220459232*alpha + 3132686016 : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (3/2 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = -96*alpha + 188)
New point of infinite order (x = -48*alpha + 60)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 2, 2 ]

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = -365312*alpha - 1261120)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (274688*alpha + 498880 : 1349120000*alpha + 571200000 : 1), (-365312*alpha -
    1261120 : -3927040000*alpha + 673600000 : 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  3  =  { (-4/3 : 1) }
[
    1/16*(-34*alpha + 17),
    1/81*(1785*alpha - 170)
]
{ (-4/3 : 1), (3/2 : 1) }

*/

//In this case we get first twist does not work for Chabauty condition
//Points already found { (1 : 1), (1 : 0), (3/2,1),(-4/3,1)}
//Remaining points {(2,1), (0,1)}

//Now we go to the 4 degree extension

deltas:=[-theta,2-theta];

K<alpha>:=NumberField((x^4 - 2*x^3 + 3*x^2 - 6*x + 5));

fac:=Factorization(ChangeRing(f,K));
fac;

/*
[
    <$.1 - alpha, 1>,
    <$.1 - alpha^3 + alpha^2 - 3*alpha + 3, 1>,
    <$.1 - alpha^3 + alpha^2 - 2*alpha + 3, 1>,
    <$.1 + alpha^3 - alpha^2 + 3*alpha - 5, 1>,
    <$.1^2 + (alpha^3 - alpha^2 + 3*alpha - 5)*$.1 - alpha^3 + alpha^2 - 3*alpha
        + 3, 1>
]
*/

g:=fac[1][1]*fac[2][1]*fac[5][1];
g;

/*
[
    -2*alpha^3 - alpha + 10,
    -5*alpha + 10
]
[
    { (0 : 1) },
    { (2 : 1) }
]

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1200000*alpha^3 - 840000*alpha^2 +
2000000*alpha - 4440000)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (560000*alpha^3 - 200000*alpha^2 + 80000*alpha + 1160000 : 1120000000*alpha^3
    - 320000000*alpha^2 + 1600000000*alpha + 320000000 : 1), (1200000*alpha^3 -
    840000*alpha^2 + 2000000*alpha - 4440000 : 2912000000*alpha^3 -
    3552000000*alpha^2 + 5056000000*alpha - 10560000000 : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (0 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = -136*alpha^3 + 124*alpha^2 - 248*alpha + 468)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-8*alpha^3 - 4*alpha^2 + 136*alpha + 164 : 576*alpha^3 + 80*alpha^2 +
    288*alpha - 1040 : 1), (-136*alpha^3 + 124*alpha^2 - 248*alpha + 468 :
    -3008*alpha^3 + 1648*alpha^2 - 6624*alpha + 7664 : 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  2  =  { (2 : 1) }
[
    -2*alpha^3 - alpha + 10,
    -5*alpha + 10
]
{ (2 : 1), (0 : 1) }

/*

//Done !!!








////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////





//N=93
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:=( x^3-2*x^2-x+3)*( x^3+2*x^2 -5*x+3 );
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};
print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (1 : 1), (2 : 1), (3/2 : 1), (1/4 : 1), (1 : 0), (-1 :1), (0 : 1) }

b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 


//We go to a degree 3 extension

K:=NumberField(Factorization(f)[2][1]);
Ff2:=Factorization(ChangeRing(f,K));
Ff2;
g:=Ff2[3][1]*Ff2[4][1];
g;
MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    -3*K.1^2 - 6*K.1 + 18,
    1/16*(-34*K.1^2 - 92*K.1 + 113)
]
[
    { (1 : 1), (1/4 : 1), (1 : 0) },
    { (2 : 1), (-1 : 1) },
    { (3/2 : 1), (0 : 1) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/3*(656*$.1^2 + 1136*$.1 - 1632))
New point of infinite order (x = 1/9*(304*$.1^2 + 464*$.1 - 1568))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/12*(-7*K.1^2 - 25*K.1 - 6) : 1/2*(3*K.1^2 + 8*K.1 - 13) : 1),
(1/12*(5*K.1^2 + 11*K.1 - 18) : 1/2*(K.1^2 - 10) : 1), (1/12*(41*K.1^2 + 71*K.1
    - 102) : 1/2*(23*K.1^2 + 20*K.1 - 45) : 1), (1/36*(19*K.1^2 + 29*K.1 - 98) :
1/54*(155*K.1^2 + 340*K.1 - 697) : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  1  =  { (1 : 1), (1/4 : 1), (1 : 0) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/3*(793*$.1^2 + 1204*$.1 - 6000))
New point of infinite order (x = 1/867*(-10031*$.1^2 - 102092*$.1 - 237792))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/3*(25*K.1^2 - 188*K.1 - 1008) : -116*K.1^2 - 988*K.1 - 2060 : 1),
(1/3*(73*K.1^2 - 188*K.1 - 1632) : 396*K.1^2 - 924*K.1 - 8508 : 1),
(1/3*(793*K.1^2 + 1204*K.1 - 6000) : -10020*K.1^2 - 41340*K.1 - 18540 : 1),
(1/867*(-10031*K.1^2 - 102092*K.1 - 237792) : 1/4913*(-5631636*K.1^2 -
    19158948*K.1 + 4310364) : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  2  =  { (-1 : 1), (2 : 1) }


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = -6*$.1^2 - 33*$.1 - 36)
New point of infinite order (x = -102*$.1^2 - 417*$.1 - 36)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (-54*K.1^2 - 297*K.1 - 324 : -756*K.1^2 - 3024*K.1 - 324 : 1), (-54*K.1^2 -
    153*K.1 + 108 : 108*K.1^2 + 432*K.1 - 1620 : 1), (-6*K.1^2 - 33*K.1 - 36 :
    -108*K.1^2 - 216*K.1 + 756 : 1), (-102*K.1^2 - 417*K.1 - 36 : -972*K.1^2 -
    5400*K.1 - 3564 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  2  =  { (3/2 : 1), (0 : 1), (-3/2 : 1) }
[
    1,
    -3*K.1^2 - 6*K.1 + 18,
    1/16*(-34*K.1^2 - 92*K.1 + 113)
]
{ (1 : 1), (1/4 : 1), (1 : 0) ,(3/2 : 1), (-3/2 : 1), (0 : 1), (-1 : 1), (2 : 1) }

*/

//Note that there is a "fake solution"  (-3/2 : 1) that in fact it is not a point of X
//but  it is just a rational solution of $y^2=tw*g(x)$


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////

//N=106



_<x>:=PolynomialRing(Rationals());

N:= 106; f:= x^6-4*x^5+4*x^4+2*x^3+4*x^2-4*x+1;
P1:=ProjectiveSpace(Rationals(),1);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (1 : 1), (2 : 1), (1 : 0), (-1 : 1), (0 : 1), (1/2 : 1)

b,deltas:=MyDeltas(X,uXrat);

b;

//true
print "Productive deltas =", deltas; 
/*
Productive deltas =[
    1,
    -theta + 1,
    -theta,
    -theta - 1
]
*/

K:=NumberField(f); 
Rf:=Roots(ChangeRing(f,K));
K:=NumberField(MinimalPolynomial(Rf[1][1]+Rf[2][1]));

Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[2][1];

/*
[
    1,
    K.1^2 - 6*K.1 + 13
]
[
    { (2 : 1), (1 : 0), (0 : 1), (1/2 : 1) },
    { (1 : 1), (-1 : 1) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/25*(364*$.1^2 - 1296*$.1 + 624))
New point of infinite order (x = 1/2209*(-30772*$.1^2 + 70256*$.1 + 195120))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/4*(-K.1^2 + 4*K.1 - 8) : 1/2*(-3*K.1^2 + 10*K.1 - 6) : 1), (1/4*(3*K.1^2 -
    8*K.1 - 12) : 0 : 1), (1/100*(91*K.1^2 - 324*K.1 + 156) : 1/250*(-301*K.1^2
    + 814*K.1 + 784) : 1), (1/4*(3*K.1^2 - 20*K.1 - 20) : 1/2*(27*K.1^2 - 42*K.1
    - 96) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (2 : 1), (1/2 : 1), (0 : 1), (1 : 0) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 2
After 2-descent:
    0 <= Rank(E) <= 0
    Sha(E)[2] is trivial

Rank for twist= 2 = [ 0, 0 ]
Solutions for twist  2  =  { (-1 : 1), (1 : 1) }
[
    1,
    K.1^2 - 6*K.1 + 13
]
{ (2 : 1), (-1 : 1), (1 : 1), (1/2 : 1), (0 : 1), (1 : 0) }

*/

//Done!!



////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////


//N=115
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);

f:=(x^3 - 2*x^2 + 3*x - 1)*(x^3 + 2*x^2 - 9*x + 7);

Ff:=Factorization(f);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (1 : 1), (2 : 1), (4/3 : 1), (1 : 0), (1/2 : 1) }

b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 


//Computation of a field where it has a degree 2 factor
K:=NumberField(Ff[1][1]);
Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[4][1]*Ff2[3][1];


MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    1/81*(135*K.1^2 - 90*K.1 + 40),
    K.1^2 + 10*K.1 - 2
]
[
    { (1 : 1), (1 : 0) },
    { (4/3 : 1), (1/2 : 1) },
    { (2 : 1) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 560*$.1^2 - 816*$.1 + 864)
New point of infinite order (x = 304*$.1^2 - 432*$.1 + 160)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/4*(11*K.1^2 - 11*K.1 + 2) : 1/2*(15*K.1^2 - 12*K.1 + 3) : 1),
(1/4*(15*K.1^2 - 31*K.1 + 14) : 1/2*(21*K.1^2 - 12*K.1 + 6) : 1), (1/4*(35*K.1^2
    - 51*K.1 + 54) : 1/2*(6*K.1^2 - 2*K.1 - 9) : 1), (1/4*(19*K.1^2 - 27*K.1 +
    10) : 1/2*(11*K.1^2 - 10*K.1 + 7) : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (1 : 1), (1 : 0) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 239*$.1^2 - 415*$.1 + 190)
New point of infinite order (x = 255*$.1^2 - 431*$.1 + 254)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (147*K.1^2 - 235*K.1 + 74 : -2220*K.1^2 + 4200*K.1 - 1400 : 1), (191*K.1^2 -
    295*K.1 + 86 : -1860*K.1^2 + 3800*K.1 - 1220 : 1), (239*K.1^2 - 415*K.1 +
    190 : -2252*K.1^2 + 4480*K.1 - 2636 : 1), (255*K.1^2 - 431*K.1 + 254 :
    -2044*K.1^2 + 4160*K.1 - 1724 : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  2  =  { (1/2 : 1), (4/3 : 1) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 456*$.1^2 - 692*$.1 + 1040)
New point of infinite order (x = -56*$.1^2 + 156*$.1 - 208)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (-88*K.1^2 + 140*K.1 - 208 : -960*K.1^2 + 1360*K.1 - 2080 : 1), (72*K.1^2 -
    100*K.1 + 32 : 720*K.1 - 640 : 1), (456*K.1^2 - 692*K.1 + 1040 : -8128*K.1^2
    + 12560*K.1 - 17888 : 1), (-56*K.1^2 + 156*K.1 - 208 : -224*K.1^2 + 624*K.1
    - 832 : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  3  =  { (1/3 : 1), (2 : 1) }
[
    1,
    1/81*(135*K.1^2 - 90*K.1 + 40),
    K.1^2 + 10*K.1 - 2
]
{ (1/3 : 1), (2 : 1), (1 : 1), (1/2 : 1), (4/3 : 1), (1 : 0) }


*/

//Again we got a "fake solution" (1/3:1)
//Done!!!


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////

//N=122 

_<x>:=PolynomialRing(Rationals());
N:= 122; f:=  x^6+4*x^4-6*x^3+4*x^2+1;
P1:=ProjectiveSpace(Rationals(),1);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (1 : 1), (3/2 : 1), (1 : 0), (-1 : 1), (0 : 1), (2/3 :1) }
b,deltas:=MyDeltas(X,uXrat);

b;

//true
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta + 1,
    -theta + 3/2,
    -theta - 1
]
*/

K:=NumberField(f); 
Rf:=Roots(ChangeRing(f,K));
K:=NumberField(MinimalPolynomial(Rf[1][1]+Rf[2][1]));

Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[2][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    K.1^2 + 2*K.1 + 5
]
[
    { (3/2 : 1), (1 : 0), (0 : 1), (2/3 : 1) },
    { (1 : 1), (-1 : 1) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 17*$.1^2 + 22*$.1 + 73)
New point of infinite order (x = 140*$.1^2 + 208*$.1 + 496)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/4*(-K.1^2 - 4*K.1 + 8) : 1/2*(K.1^2 - 2*K.1 + 6) : 1), (1/4*(3*K.1^2 + 4) :
0 : 1), (1/16*(17*K.1^2 + 22*K.1 + 73) : 1/64*(-127*K.1^2 - 306*K.1 - 411) : 1),
(1/4*(35*K.1^2 + 52*K.1 + 124) : 1/2*(-149*K.1^2 - 246*K.1 - 552) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (2/3 : 1), (3/2 : 1), (0 : 1), (1 : 0) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 2
After 2-descent:
    0 <= Rank(E) <= 0
    Sha(E)[2] is trivial

Rank for twist= 2 = [ 0, 0 ]
Solutions for twist  2  =  { (-1 : 1), (1 : 1) }
[
    1,
    K.1^2 + 2*K.1 + 5
]
{ (2/3 : 1), (3/2 : 1), (-1 : 1), (1 : 1), (0 : 1), (1 : 0) }


*/

//Done!!


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////

//N=129 
_<x>:=PolynomialRing(Rationals());
N:= 129; f:= x^6-4*x^5-4*x^4+12* x^3+4*x^2-12*x+4;

P1:=ProjectiveSpace(Rationals(),1);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (1 : 1), (7/12 : 1), (-7/5 : 1), (1 : 0), (-1 : 1), (0 :1), (1/2 : 1) }


b,deltas:=MyDeltas(X,uXrat);

b;

//true
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta - 1
]
*/

K:=NumberField(f); 
Rf:=Roots(ChangeRing(f,K));
K:=NumberField(MinimalPolynomial(Rf[1][1]+Rf[2][1]));

Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[2][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    4*K.1^2 - 18*K.1 - 23
]
[
    { (1 : 1), (7/12 : 1), (-7/5 : 1), (1 : 0), (0 : 1) },
    { (-1 : 1), (1/2 : 1) }
]


Torsion Subgroup = Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = 1/177241*(-32452160*$.1^2 + 149242112*$.1 +
177172480))
New point of infinite order (x = -2112*$.1^2 + 10496*$.1 + 7168)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z + Z
Defined on 3 generators
Relations:
    2*G.1 = 0
[ (1/4*(3*K.1^2 - 8*K.1 - 48) : 1/2*(3*K.1^2 - 8*K.1 - 48) : 1),
(1/708964*(-507065*K.1^2 + 2331908*K.1 + 2768320) : 1/74618461*(-373889483*K.1^2
    + 1610101854*K.1 + 2627550838) : 1), (1/4*(-33*K.1^2 + 164*K.1 + 112) :
    -39*K.1^2 + 200*K.1 + 94 : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (7/12 : 1), (-7/5 : 1), (1 : 1), (0 : 1), (1 : 0) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = -84*$.1^2 + 400*$.1 + 320)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-52*K.1^2 + 288*K.1 + 256 : 416*K.1^2 - 2304*K.1 - 2048 : 1), (-84*K.1^2 +
    400*K.1 + 320 : 1472*K.1^2 - 4864*K.1 - 4096 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  2  =  { (2 : 1), (-1 : 1), (1/2 : 1) }
[
    1,
    4*K.1^2 - 18*K.1 - 23
]
{ (7/12 : 1), (-7/5 : 1), (2 : 1), (1 : 1), (-1 : 1), (1/2 : 1), (0 : 1), (1 : 0) }
*/



//Done!!


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////



//N=154
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:=(x - 2)*(x^2 + x + 2)*(x^3 - 3*x^2 - x - 1);

X:=HyperellipticCurve(f);
Ff:=Factorization(f);
Ff;
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (1 : 1), (2 : 1), (-1/3 : 1), (-3/2 : 1), (4 : 1), (1 : 0), (0 : 1) }

b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 


//We try if there is one covering already over Q

g:=Ff[1][1]*Ff[3][1];
MyEllipticChabauty(g,deltas,uXrat);
/*
[ 1, 539/16, 22, 98 ]
[
    { (1 : 1), (2 : 1), (-1/3 : 1), (1 : 0) },
    { (2 : 1), (-3/2 : 1) },
    { (2 : 1), (4 : 1) },
    { (2 : 1), (0 : 1) }
]


Torsion Subgroup is trivial
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 1 = [ 1, 1 ]

Torsion Subgroup is trivial
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 2 = [ 1, 1 ]

Torsion Subgroup is trivial
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 3 = [ 1, 1 ]

Torsion Subgroup is trivial
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 4 = [ 1, 1 ]
[]
{}
*/
//All twists have rank 1. No point is done 

//We go to a degree 2 field

K:=NumberField(Ff[2][1]);
Ff2:=Factorization(ChangeRing(f,K));

Ff2;
/*
[
    <$.1 - 2, 1>,
    <$.1 - K.1, 1>,
    <$.1 + K.1 + 1, 1>,
    <$.1^3 - 3*$.1^2 - $.1 - 1, 1>
]
*/

g:=Ff2[2][1]*Ff2[4][1];



MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    1/16*(154*K.1 + 231),
    -11*K.1 + 44,
    -98*K.1 - 98
]
[
    { (1 : 1), (-1/3 : 1), (1 : 0) },
    { (-3/2 : 1) },
    { (4 : 1) },
    { (2 : 1), (0 : 1) }
]


Torsion Subgroup = Z/3
The 2-Selmer group has rank 1
New point of infinite order (x = 3*$.1 - 15)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z/3 + Z
Defined on 2 generators
Relations:
    3*G.1 = 0
[ (1/4*(19*K.1 + 1) : 1/2*(-5*K.1 + 9) : 1), (1/4*(3*K.1 - 15) : 1/2*(-K.1 + 5)
: 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  1  =  { (-1/3 : 1), (1 : 1), (1 : 0) }

Torsion Subgroup is trivial
The 2-Selmer group has rank 1
New point of infinite order (x = -19845*$.1 - 12231)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z
Defined on 1 generator (free)
[ (-19845*K.1 - 12231 : -5177844*K.1 - 2088828 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  2  =  { (-3/2 : 1) }

Torsion Subgroup is trivial
The 2-Selmer group has rank 1
New point of infinite order (x = -1040*$.1 - 14768)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z
Defined on 1 generator (free)
[ (-1040*K.1 - 14768 : -211328*K.1 + 151424 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  3  =  { (4 : 1) }

Torsion Subgroup is trivial
The 2-Selmer group has rank 1
New point of infinite order (x = 15*$.1 + 101)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 4 = [ 1, 1 ]
Abelian Group isomorphic to Z
Defined on 1 generator (free)
[ (-K.1 + 37 : -148*K.1 - 156 : 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  4  =  { (2 : 1), (0 : 1) }
[
    1,
    1/16*(154*K.1 + 231),
    -11*K.1 + 44,
    -98*K.1 - 98
]
{ (4 : 1), (2 : 1), (-1/3 : 1), (1 : 1), (-3/2 : 1), (0 : 1), (1 : 0) }

*/


//Done!!!


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////



//N=158
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
N:= 158; f:= x^6-4*x^4+2*x^3-4*x^2+1; 

P1:=ProjectiveSpace(Rationals(),1);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (2 : 1), (1 : 0), (0 : 1), (1/2 : 1) }

b,deltas:=MyDeltas(X,uXrat);

b;

//true
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta
]
*/

K:=NumberField(f); 
Rf:=Roots(ChangeRing(f,K));
K:=NumberField(MinimalPolynomial(Rf[1][1]+Rf[2][1]));

Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[2][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
Torsion Subgroup = Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = 28*$.1^2 - 32*$.1 - 48)
New point of infinite order (x = 12*$.1^2 - 48)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z + Z
Defined on 3 generators
Relations:
    2*G.1 = 0
[ (1/4*(3*K.1^2 - 28) : 0 : 1), (1/4*(7*K.1^2 - 8*K.1 - 12) : 1/2*(-4*K.1^2 +
    15*K.1 - 10) : 1), (1/4*(3*K.1^2 - 12) : -4*K.1 : 1) ]
supp(R) = [ 2, 3, 5, 7 ]
Verify Saturation= true
Solutions for twist  1  =  { (2 : 1), (1/2 : 1), (0 : 1), (1 : 0) }
[
    1
]
{ (2 : 1), (1/2 : 1), (0 : 1), (1 : 0) }
*/


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////

//N=161
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:=(x^3 - 2*x^2 + 3*x - 1)*(x^3 + 2*x^2 + 3*x - 5);


Ff:=Factorization(f);

X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (1 : 1), (-1/2 : 1), (-1/4 : 1), (1 : 0), (-1 : 1) }


b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
/*
Productive deltas = [
    1,
    -theta - 1,
    -theta - 1/2
]
*/

//Computation of a field where it has a degree 2 factor
K:=NumberField(Ff[1][1]);
Ff2:=Factorization(ChangeRing(f,K));

Ff2;
/*
[
    <$.1 - K.1, 1>,
    <$.1 - K.1^2 + 3*K.1 - 2, 1>,
    <$.1^2 + (K.1 - 2)*$.1 + K.1^2 - 2*K.1 + 3, 1>,
    <$.1^2 + (K.1^2 - 3*K.1 + 4)*$.1 + 4*K.1^2 - 5*K.1 + 7, 1>
]
*/

g:=Ff2[4][1]*Ff2[3][1];


MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    9*K.1^2 - 6*K.1 + 19,
    1/16*(126*K.1^2 - 140*K.1 + 273)
]
[
    { (1 : 1), (-1/4 : 1), (1 : 0) },
    { (-1 : 1) },
    { (-1/2 : 1) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1072*$.1^2 - 1584*$.1 + 1824)
New point of infinite order (x = -80*$.1^2 - 48*$.1 + 32)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/4*(-13*K.1^2 + 29*K.1 - 30) : 1/2*(7*K.1^2 - 4*K.1 + 15) : 1),
(1/4*(3*K.1^2 - 3*K.1 + 2) : 1/2*(3*K.1^2 + 7) : 1), (1/4*(67*K.1^2 - 99*K.1 +
    114) : 1/2*(-81*K.1^2 + 176*K.1 - 233) : 1), (1/4*(-5*K.1^2 - 3*K.1 + 2) :
1/2*(K.1^2 + 22*K.1 + 7) : 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  1  =  { (-1/4 : 1), (1 : 1), (1 : 0) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = 0)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z
Defined on 3 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (-37*K.1^2 + 20*K.1 - 48 : -868*K.1^2 + 868*K.1 - 1596 : 1), (27*K.1^2 -
    60*K.1 + 32 : 492*K.1^2 - 972*K.1 + 356 : 1), (0 : 8*K.1^2 + 326*K.1 - 634 :
1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  2  =  { (-1 : 1) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = 1/39980329*(185066269583*$.1^2 -
254402906495*$.1 + 279530991838))
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z
Defined on 3 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (-1673*K.1^2 + 345*K.1 - 2578 : -504300*K.1^2 + 288600*K.1 - 961500 : 1),
(2027*K.1^2 - 3755*K.1 + 6322 : 779100*K.1^2 - 1272600*K.1 + 2095800 : 1),
(1/39980329*(185066269583*K.1^2 - 254402906495*K.1 + 279530991838) :
1/252795620267*(399799562689191900*K.1^2 - 524442114302383800*K.1 +
    573313217747599500) : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  3  =  { (-1/2 : 1) }
[
    1,
    9*K.1^2 - 6*K.1 + 19,
    1/16*(126*K.1^2 - 140*K.1 + 273)
]
{ (-1/4 : 1), (-1/2 : 1), (1 : 1), (-1 : 1), (1 : 0) }

*/


//Done !!!!

////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////






///N=165  
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);

f:=(x-1)*(x + 3)*(x^2- x- 1)*(x^2 - x + 3);


X:=HyperellipticCurve(f);
Ff:=Factorization(f);
Ff;
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (1 : 0), (2 : 1), (1 : 1), (-1/2 : 1), (0 : 1), (5/2 : 1), (2/3 : 1), (-3 : 1) }
b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta,
    -theta - 1/2,
    -theta + 2,
    -2162/165*theta^5 - 753/55*theta^4 + 1303/33*theta^3 - 2920/33*theta^2 +
        18662/165*theta + 7023/55,
    -theta + 5/2,
    -theta + 2/3,
    14/55*theta^5 + 13/55*theta^4 - 8/11*theta^3 + 19/11*theta^2 - 179/55*theta
        - 68/55
]
*/

//First we try if there is one covering already over Q
//We find there is no one (all covers have rang 1).

//


//We try a covering defined over the quadratic extension for the second degree 2 factor

K<alpha>:=NumberField(Ff[4][1]);
Ff2:=Factorization(ChangeRing(f,K));
Ff2;


g:=Ff2[1][1]*Ff2[3][1]*Ff2[5][1];
g;


MyEllipticChabauty(g,deltas,uXrat);


/*

[
    1,
    -alpha,
    1/16*(-6*alpha - 3),
    -alpha + 2,
    16335*alpha - 65340,
    1/16*(-66*alpha + 165)
]
[
    { (1 : 1), (1 : 0), (2/3 : 1) },
    { (1 : 1), (0 : 1) },
    { (1 : 1), (-1/2 : 1) },
    { (1 : 1), (2 : 1) },
    { (1 : 1), (-3 : 1) },
    { (1 : 1), (5/2 : 1) }
]


Torsion Subgroup = Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = 1/25*(-148*alpha + 332))
New point of infinite order (x = 1/9*(-100*alpha - 20))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 0)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-alpha + 3 : 0 : 1), (0 : 3*alpha : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  2  =  { (1 : 1), (0 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = -16*alpha + 112)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-144*alpha + 288 : 0 : 1), (-16*alpha + 112 : 704*alpha + 832 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  3  =  { (-1/2 : 1), (1 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 4*alpha + 2)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 4 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (alpha + 3 : 0 : 1), (4*alpha + 2 : -alpha - 8 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  4  =  { (2 : 1), (1 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = -170973*alpha + 177507)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 5 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-49005*alpha - 49005 : 0 : 1), (-170973*alpha + 177507 : 49736808*alpha -
    73886472 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  5  =  { (1 : 1), (-3 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 501875*alpha - 3103125)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 6 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (501875*alpha - 875625 : 381150000*alpha + 605137500 : 1), (501875*alpha -
    3103125 : -1456537500*alpha + 1206562500 : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  6  =  { (1 : 1), (5/2 : 1) }
[
    -alpha,
    1/16*(-6*alpha - 3),
    -alpha + 2,
    16335*alpha - 65340,
    1/16*(-66*alpha + 165)
]
{ (-1/2 : 1), (2 : 1), (1 : 1), (0 : 1), (-3 : 1), (5/2 : 1) }

*/



//So all the twists except the first one succedd. 
//The deltas that remain are the ones corresponding 
//to the points [1:0] and [2/3:1]
deltas:=[1,2/3-theta];

//We try now the othe degree two extension, but only this deltas


//
K<alpha>:=NumberField(Ff[3][1]);

Ff:=Factorization(ChangeRing(f,K));
Ff;
g:=Ff[1][1]*Ff[3][1]*Ff[5][1];
/*
Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-19900*alpha - 32776 : 14630000*alpha + 10788800 : 1), (-19900*alpha + 112424
: -7150000*alpha - 7506400 : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  2  =  { (2/3 : 1), (1 : 1) }
[
    1/81*(75*alpha - 50)
]
{ (2/3 : 1), (1 : 1) }

*/

//It remains still the delta=1
deltas:=[A!1];

//We go to the extension where f factorizes completely

K<alpha>:=Compositum(NumberField(Ff[4][1]),NumberField(Ff[3][1]));

Ff:=Factorization(ChangeRing(f,K));
Ff;


g:=Ff[1][1]*Ff[2][1]*Ff[3][1]*Ff[5][1];
g;


MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1
]
[
    { (1 : 1), (-3 : 1), (1 : 0) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 36*alpha^3 - 88*alpha^2 + 80*alpha - 256)
New point of infinite order (x = 1/961*(-11008*alpha^3 + 9796*alpha^2 +
9304*alpha - 183536))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/4*(-alpha^2 - 4*alpha - 4) : 1/4*(-alpha^3 - alpha^2 - 6*alpha - 16) : 1),
(1/4*(-2*alpha^3 + 7*alpha^2 - 14*alpha - 4) : 1/4*(alpha^3 - 5*alpha^2 -
    6*alpha + 4) : 1), (1/4*(9*alpha^3 - 22*alpha^2 + 20*alpha - 64) :
1/8*(-11*alpha^3 - 167*alpha^2 - 66*alpha - 452) : 1), (1/3844*(-2752*alpha^3 +
    2449*alpha^2 + 2326*alpha - 45884) : 1/59582*(130216*alpha^3 -
    559333*alpha^2 + 962322*alpha + 589292) : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (1 : 1), (-3 : 1), (1 : 0) }
[
    1
]
{ (1 : 1), (-3 : 1), (1 : 0) }

*/


//Done!!!



////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////



//N=170
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:=(x^2 - 5*x + 5)*(x^4 - 11*x^3 + 48*x^2 - 87*x + 53);


X:=HyperellipticCurve(f);
Ff:=Factorization(f);
Ff;
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (1 : 1), (2 : 1), (3/2 : 1), (11/3 : 1), (4 : 1), (1 :0) }

b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 


//We try first the case K=Q
//We get rank 1 in all twists (just 2)




//We go to a degree 4 field

K:=NumberField(Ff[2][1]);
Ff2:=Factorization(ChangeRing(f,K));

Ff2;
/*
[
    <$.1 - K.1, 1>,
    <$.1 + 1/5*(K.1^3 - 7*K.1^2 + 20*K.1 - 27), 1>,
    <$.1^2 - 5*$.1 + 5, 1>,
    <$.1^2 + 1/5*(-K.1^3 + 7*K.1^2 - 15*K.1 - 28)*$.1 + 1/5*(4*K.1^3 - 28*K.1^2
        + 60*K.1 + 57), 1>
]
*/

g:=Ff2[3][1]*Ff2[4][1];
MyEllipticChabauty(g,deltas,uXrat);
/*
[
    1,
    1/16*(-2*K.1^3 + 14*K.1^2 - 30*K.1 - 21),
    5,
    1/5*(-2*K.1^3 + 14*K.1^2 - 30*K.1 - 21)
]
[
    { (1 : 1), (11/3 : 1), (1 : 0) },
    { (3/2 : 1) },
    { (4 : 1) },
    { (2 : 1) }
]


Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/5*(3*$.1^3 - 21*$.1^2 + 45*$.1 - 11))
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/20*(-K.1^3 + 7*K.1^2 - 15*K.1 - 23) : 1/5*(-4*K.1^3 + 28*K.1^2 - 60*K.1 -
    52) : 1), (1/20*(3*K.1^3 - 21*K.1^2 + 45*K.1 - 11) : 1/10*(7*K.1^3 -
    49*K.1^2 + 105*K.1 + 1) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (11/3 : 1), (1 : 1), (1 : 0) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/85*(41391*$.1^3 - 289737*$.1^2 + 620865*$.1 -
1154007))
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/5*(-1377*K.1^3 + 9639*K.1^2 - 20655*K.1 - 31671) : 21384*K.1^3 -
    149688*K.1^2 + 320760*K.1 + 258552 : 1), (1/85*(41391*K.1^3 - 289737*K.1^2 +
    620865*K.1 - 1154007) : 1/289*(4235976*K.1^3 - 29651832*K.1^2 + 63539640*K.1
    + 90273528) : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  2  =  { (3/2 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 0)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (-320*K.1^3 + 2240*K.1^2 - 4800*K.1 - 10432 : 4608*K.1^3 - 32256*K.1^2 +
    69120*K.1 - 98816 : 1), (0 : 1/5*(201728*K.1^3 - 1412096*K.1^2 + 3025920*K.1
    + 8817664) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  3  =  { (4 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/5*(44*$.1^3 - 308*$.1^2 + 660*$.1 - 348))
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 4 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/5*(28*K.1^3 - 196*K.1^2 + 420*K.1 - 316) : 1/5*(208*K.1^3 - 1456*K.1^2 +
    3120*K.1 - 1616) : 1), (1/5*(44*K.1^3 - 308*K.1^2 + 660*K.1 - 348) :
1/5*(208*K.1^3 - 1456*K.1^2 + 3120*K.1 - 2896) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  4  =  { (2 : 1) }
[
    1,
    1/16*(-2*K.1^3 + 14*K.1^2 - 30*K.1 - 21),
    5,
    1/5*(-2*K.1^3 + 14*K.1^2 - 30*K.1 - 21)
]
{ (4 : 1), (11/3 : 1), (3/2 : 1), (2 : 1), (1 : 1), (1 : 0) }


*/

//Done!!!









////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////

//N=186  

_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:=(x^3 - 2* x^2 + x + 1)*(x^3 + 2*x^2 + 5*x + 1);

Ff:=Factorization(f);

X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (1 : 0), (-1 : 1), (2 : 1), (-4/3 : 1), (1 : 1), (-1/2 : 1), (0 : 1) }

b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta + 2,
    -theta + 1
]
*/

//Computation of a field where it has a degree 2 factor
K:=NumberField(Ff[1][1]);
Ff2:=Factorization(ChangeRing(f,K));

Ff2;
/*
[
    <$.1 - K.1, 1>,
    <$.1 + K.1^2, 1>,
    <$.1^2 + (K.1 - 2)*$.1 + K.1^2 - 2*K.1 + 1, 1>,
    <$.1^2 + (-K.1^2 + 2)*$.1 + K.1^2 - 3*K.1 + 3, 1>
]
*/

g:=Ff2[4][1]*Ff2[3][1];

MyEllipticChabauty(g,deltas,uXrat);


/*
[
    1,
    K.1^2 + 3*K.1 + 16,
    3*K.1^2 - 3*K.1 + 3
]
[
    { (-4/3 : 1), (1 : 0), (0 : 1) },
    { (2 : 1), (-1 : 1) },
    { (1 : 1), (-1/2 : 1) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/9*(512*$.1^2 + 1104*$.1 - 1600))
New point of infinite order (x = 144*$.1 - 192)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/4*(-3*K.1 + 4) : 1/2*(K.1^2 - 7*K.1 + 11) : 1), (1/4*(13*K.1 - 12) :
1/2*(K.1^2 - 7*K.1 + 7) : 1), (1/36*(32*K.1^2 + 69*K.1 - 100) : 1/54*(-95*K.1^2
    + 93*K.1 - 35) : 1), (1/4*(9*K.1 - 12) : 0 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  1  =  { (-4/3 : 1), (0 : 1), (1 : 0) }


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 661932*$.1^2 - 139968*$.1 - 23328)
New point of infinite order (x = 3391308*$.1^2 - 6543504*$.1 + 6275232)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (32076*K.1^2 + 1434672*K.1 - 653184 : -1130906448*K.1^2 + 2091751776*K.1 -
    2159776224 : 1), (451980*K.1^2 - 1084752*K.1 + 1446336 : -768109392*K.1^2 +
    2363849568*K.1 - 3406891104 : 1), (661932*K.1^2 - 139968*K.1 - 23328 :
    -2474389296*K.1^2 + 5220876384*K.1 - 4880754144 : 1), (3391308*K.1^2 -
    6543504*K.1 + 6275232 : 3336032304*K.1^2 - 8780822496*K.1 + 7567719840 : 1)
]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  2  =  { (-1 : 1), (-2/5 : 1), (2 : 1) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/289*(-3171*$.1^2 - 865*$.1 + 8538))
New point of infinite order (x = 1/6889*(462325*$.1^2 - 1243153*$.1 + 1164178))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (-19*K.1^2 + 23*K.1 + 2 : 152*K.1^2 - 276*K.1 + 164 : 1), (-3*K.1^2 - 25*K.1 +
    18 : 24*K.1^2 + 204*K.1 - 108 : 1), (1/289*(-3171*K.1^2 - 865*K.1 + 8538) :
1/4913*(352320*K.1^2 + 84612*K.1 - 843636) : 1), (-19*K.1^2 + 23*K.1 + 10 :
    112*K.1^2 - 180*K.1 - 28 : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  3  =  { (-1/2 : 1), (1 : 1) }
[
    1,
    K.1^2 + 3*K.1 + 16,
    3*K.1^2 - 3*K.1 + 3
]
{  (-4/3 : 1), (0 : 1), (1 : 0), (-1 : 1), (-1/2 : 1), (-2/5 : 1), (2 : 1), (1 : 1) }

*/

//Note that there is a "fake solution" (-2/5:1). 
//Done !!!



////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////



//N=209
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
N:= 209; f:=  x^6-4*x^5+8*x^4-8*x^3+8*x^2+4*x+4; 
P1:=ProjectiveSpace(Rationals(),1);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (-1/2 : 1), (1 : 0), (0 : 1) }
b,deltas:=MyDeltas(X,uXrat);

b;

//true
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta - 1/2
]
*/

K:=NumberField(f); 
Rf:=Roots(ChangeRing(f,K));
K:=NumberField(MinimalPolynomial(Rf[1][1]+Rf[2][1]));

Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[2][1];

MyEllipticChabauty(g,deltas,uXrat: IndexBound:=2*3*5*7);

/*
[
    1,
    1/16*(-38*K.1 + 57)
]
[
    { (1 : 0), (0 : 1) },
    { (-1/2 : 1) }
]


Torsion Subgroup = Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = -320*$.1^2 + 1280*$.1 - 2048)
New point of infinite order (x = -64*$.1^2 - 256*$.1)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z + Z
Defined on 3 generators
Relations:
    2*G.1 = 0
[ (1/4*(3*K.1^2 - 8*K.1 + 16) : 1/2*(-K.1^2 + 4) : 1), (1/4*(-5*K.1^2 + 20*K.1 -
    32) : -5*K.1^2 + 16*K.1 - 22 : 1), (1/4*(-K.1^2 - 4*K.1) : -2*K.1^2 + 2*K.1
: 1) ]
supp(R) = [ 2, 7 ]
Verify Saturation= true
Solutions for twist  1  =  { (2 : 1), (0 : 1), (1 : 0) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 0)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (268*K.1^2 - 992*K.1 + 2048 : 16416*K.1^2 - 63232*K.1 + 128896 : 1), (0 :
    4288*K.1^2 - 11520*K.1 + 26688 : 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  2  =  { (-1/2 : 1) }
[
    1,
    1/16*(-38*K.1 + 57)
]
{ (-1/2 : 1), (2 : 1), (0 : 1), (1 : 0) }

*/

//Done!!


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////


// N=215


//N=215
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
N:= 215; f:=   x^6+4*x^5-12*x^4+20*x^3-20*x^2+12*x-4;
P1:=ProjectiveSpace(Rationals(),1);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (1 : 1), (2 : 1), (1 : 0) }

b,deltas:=MyDeltas(X,uXrat);

b;

//true
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta + 2
]
*/

K:=NumberField(f); 
Rf:=Roots(ChangeRing(f,K));
K:=NumberField(MinimalPolynomial(Rf[1][1]+Rf[2][1]));

Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[2][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    K.1^2 + 8*K.1 + 24
]
[
    { (1 : 1), (1 : 0) },
    { (2 : 1) }
]


Torsion Subgroup = Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = 1/6241*(2257088*$.1^2 + 7938816*$.1 -
25675776))
New point of infinite order (x = 704*$.1^2 + 2816*$.1 - 6144)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z + Z
Defined on 3 generators
Relations:
    2*G.1 = 0
[ (1/4*(3*K.1^2 + 8*K.1 - 48) : 1/2*(3*K.1^2 + 8*K.1 - 48) : 1),
(1/24964*(35267*K.1^2 + 124044*K.1 - 401184) : 1/493039*(1606870*K.1^2 +
    6682552*K.1 - 12574068) : 1), (1/4*(11*K.1^2 + 44*K.1 - 96) : -6*K.1^2 -
    32*K.1 + 8 : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (1 : 1), (0 : 1), (1 : 0) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 1
After 2-descent:
    0 <= Rank(E) <= 0
    Sha(E)[2] is trivial

Rank for twist= 2 = [ 0, 0 ]
Solutions for twist  2  =  { (2 : 1) }
[
    1,
    K.1^2 + 8*K.1 + 24
]
{ (2 : 1), (1 : 1), (0 : 1), (1 : 0) }
*/

//Done!!!


////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////


// N=230

_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:=(x^3 - 2*x^2 + 5*x + 1)*(x^3 + 2*x^2 + x + 1);

Ff:=Factorization(f);

X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (1 : 1), (-2 : 1), (3 : 1), (1 : 0), (0 : 1) }

b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta - 2,
    -theta + 1
]
*/

//Computation of a field where it has a degree 2 factor
K:=NumberField(Ff[1][1]);
Ff2:=Factorization(ChangeRing(f,K));

Ff2;
/*
[
    <$.1 - K.1, 1>,
    <$.1 + 1/5*(K.1^2 - 4*K.1 + 8), 1>,
    <$.1^2 + (K.1 - 2)*$.1 + K.1^2 - 2*K.1 + 5, 1>,
    <$.1^2 + 1/5*(-K.1^2 + 4*K.1 + 2)*$.1 + 1/5*(K.1^2 + K.1 + 3), 1>
]
*/

g:=Ff2[4][1]*Ff2[3][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    9*K.1^2 - 21*K.1 + 52,
    3*K.1^2 - 3*K.1 + 7
]
[
    { (1 : 0), (0 : 1) },
    { (-2 : 1), (3 : 1) },
    { (1 : 1) }
]


Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/5*(64*$.1^2 + 144*$.1 + 192))
New point of infinite order (x = 1/5*(-192*$.1^2 + 1168*$.1 + 64))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (1/20*(4*K.1^2 - 11*K.1 + 32) : 1/10*(-K.1^2 - K.1 - 28) : 1), (1/20*(4*K.1^2
    + 9*K.1 - 28) : 1/10*(-11*K.1^2 + 29*K.1 - 53) : 1), (1/20*(4*K.1^2 + 9*K.1
    + 12) : 1/10*(3*K.1^2 - 17*K.1 - 1) : 1), (1/20*(-12*K.1^2 + 73*K.1 + 4) :
1/10*(-31*K.1^2 + 69*K.1 + 7) : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (0 : 1), (1 : 0) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/529*(89772*$.1^2 - 149200*$.1 - 40800))
New point of infinite order (x = 332*$.1^2 - 624*$.1 + 96)
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (188*K.1^2 - 400*K.1 - 80 : 2960*K.1^2 - 3040*K.1 - 640 : 1), (236*K.1^2 -
    528*K.1 - 128 : 1360*K.1^2 + 1760*K.1 + 160 : 1), (1/529*(89772*K.1^2 -
    149200*K.1 - 40800) : 1/12167*(51791280*K.1^2 - 132705440*K.1 - 26788640) :
1), (332*K.1^2 - 624*K.1 + 96 : -1008*K.1^2 + 1888*K.1 - 1312 : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  2  =  { (3 : 1), (-2 : 1) }

Torsion Subgroup = Z/2 x Z/2
The 2-Selmer group has rank 4
New point of infinite order (x = 1/5*(173*$.1^2 - 397*$.1 + 954))
New point of infinite order (x = 1/605*(773*$.1^2 + 803*$.1 - 3846))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z/2 + Z + Z
Defined on 4 generators
Relations:
    2*G.1 = 0
    2*G.2 = 0
[ (-7*K.1^2 + 15*K.1 - 38 : 104*K.1^2 - 236*K.1 + 572 : 1), (5*K.1^2 - 13*K.1 -
    2 : -32*K.1^2 + 148*K.1 + 64 : 1), (1/5*(173*K.1^2 - 397*K.1 + 954) :
    -32*K.1^2 + 92*K.1 - 300 : 1), (1/605*(773*K.1^2 + 803*K.1 - 3846) :
1/1331*(-74080*K.1^2 + 62524*K.1 + 36) : 1) ]
supp(R) = [ 2, 5 ]
Verify Saturation= true
Solutions for twist  3  =  { (1 : 1), (-3/2 : 1) }
[
    1,
    9*K.1^2 - 21*K.1 + 52,
    3*K.1^2 - 3*K.1 + 7
]
{ (3 : 1), (1 : 1), (0 : 1), (-2 : 1), (-3/2 : 1), (1 : 0) }





*/

//Done!!




////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////



//N=285

_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:= x*(x^2 + x + 4)*(x^3 - x^2 - x - 3);

Ff:=Factorization(f);
Ff;
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (3 : 1), (-3/2 : 1), (1 : 0), (-1 : 1), (0 : 1) }

b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta - 3/2,
    -14/57*theta^5 + 7/19*theta^4 - 31/57*theta^3 + 130/57*theta^2 - 40/57*theta
        + 1,
    -theta - 1,
    -theta + 3
]
*/


//We go to a degree 2 extension. 

K<alpha>:=NumberField(Ff[2][1]);
fac:=Factorization(ChangeRing(f,K));
fac;
/*
[
    <$.1, 1>,
    <$.1 - alpha, 1>,
    <$.1 + alpha + 1, 1>,
    <$.1^3 - $.1^2 - $.1 - 3, 1>
]
*/

g:=fac[2][1]*fac[4][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    1/16*(114*alpha + 171),
    4*alpha + 4
]
[
    { (1 : 0), (0 : 1) },
    { (-3/2 : 1) },
    { (3 : 1), (-1 : 1) }
]


Torsion Subgroup is trivial
The 2-Selmer group has rank 1
New point of infinite order (x = -5*alpha - 17)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z
Defined on 1 generator (free)
[ (1/4*(-5*alpha - 17) : -6*alpha + 10 : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  1  =  { (0 : 1), (1 : 0) }

Torsion Subgroup is trivial
The 2-Selmer group has rank 1
New point of infinite order (x = -9585*alpha + 1395)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z
Defined on 1 generator (free)
[ (351*alpha + 531 : 39852*alpha + 120636 : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  2  =  { (-3/2 : 1) }

Torsion Subgroup is trivial
The 2-Selmer group has rank 1
New point of infinite order (x = -11*alpha + 52)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z
Defined on 1 generator (free)
[ (5*alpha + 36 : 204*alpha + 496 : 1) ]
supp(R) = [ 2, 3, 5 ]
Verify Saturation= true
Solutions for twist  3  =  { (-1 : 1), (3 : 1) }
[
    1,
    1/16*(114*alpha + 171),
    4*alpha + 4
]
{ (-1 : 1), (3 : 1), (0 : 1), (-3/2 : 1), (1 : 0) }

*/

//Done !!!

////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////









//N=286

_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
f:=(x^3 - x^2 + 3*x + 1)*(x^3 + x^2 - 4);
Ff:=Factorization(f);

X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;

//Set of x-coordinates: { (5/2 : 1), (1 : 0), (-1 : 1) }
b,deltas:=MyDeltas(X,uXrat);

print "All deltas are productive? ", b;
//true 
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta + 5/2
]
*/

//Computation of a field where it has a degree 2 factor
K:=NumberField(Ff[1][1]);
Ff2:=Factorization(ChangeRing(f,K));

Ff2;
/*
[
    <$.1 - K.1, 1>,
    <$.1^2 + (K.1 - 1)*$.1 + K.1^2 - K.1 + 3, 1>,
    <$.1^3 + $.1^2 - 4, 1>
]
*/
g:=Ff2[1][1]*Ff2[3][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    1/16*(-286*K.1 + 715)
]
[
    { (1 : 0), (-1 : 1) },
    { (5/2 : 1) }
]


Torsion Subgroup is trivial
The 2-Selmer group has rank 2
New point of infinite order (x = -320*$.1^2 + 384*$.1 - 320)
New point of infinite order (x = 1/49*(-16192*$.1^2 + 39296*$.1 - 13120))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z + Z
Defined on 2 generators (free)
[ (1/4*(-5*K.1^2 + 6*K.1 - 5) : 2*K.1^2 + 2*K.1 + 2 : 1), (1/4*(3*K.1^2 - 10*K.1
    + 3) : 2*K.1 + 8 : 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  1  =  { (-1 : 1), (1 : 0) }

Torsion Subgroup is trivial
The 2-Selmer group has rank 3
New point of infinite order (x = 327500*$.1^2 - 45000*$.1 - 212500)
After 2-descent:
    1 <= Rank(E) <= 3
    Sha(E)[2] <= (Z/2)^2
(Searched up to height 16 on the 2-coverings.)
The Cassels-Tate pairing on Sel(2,E)/E[2] is
    [0 1 1]
    [1 0 0]
    [1 0 0]
After using Cassels-Tate:
    1 <= Rank(E) <= 1
    (Z/2)^2 <= Sha(E)[4] <= (Z/2)^2

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z
Defined on 1 generator (free)
[ (327500*K.1^2 - 45000*K.1 - 212500 : 156600000*K.1^2 - 1180800000*K.1 +
    1579000000 : 1) ]
supp(R) = [ 2 ]
Verify Saturation= true
Solutions for twist  2  =  { (5/2 : 1) }
[
    1,
    1/16*(-286*K.1 + 715)
]
{ (-1 : 1), (1 : 0), (5/2 : 1) }


*/



///Done!






////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////



//N=357
_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);
N:= 357; f:= x^6+8*x^4-8*x^3+20*x^2-12*x +12; 
P1:=ProjectiveSpace(Rationals(),1);
X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
Xrat;
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (2 : 1), (1 : 0) }
b,deltas:=MyDeltas(X,uXrat);

b;

//true
print "Productive deltas =", deltas; 
/*
Productive deltas = [
    1,
    -theta + 2
]
*/

K:=NumberField(f); 
Rf:=Roots(ChangeRing(f,K));
K:=NumberField(MinimalPolynomial(Rf[1][1]+Rf[2][1]));

Ff2:=Factorization(ChangeRing(f,K));

Ff2;

g:=Ff2[2][1];

MyEllipticChabauty(g,deltas,uXrat: IndexBound:=2*3*5*13);

/*

[
    1,
    1/3*(7*K.1^2 + 28*K.1 + 112)
]
[
    { (1 : 0) },
    { (2 : 1) }
]

Torsion Subgroup = Z/2
The 2-Selmer group has rank 3
New point of infinite order (x = 1/4*(19*$.1^2 + 4*$.1 + 240))
New point of infinite order (x = 1/273612*(-29047*$.1^2 - 115492*$.1 + 548144))
After 2-descent:
    2 <= Rank(E) <= 2
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 2, 2 ]
Abelian Group isomorphic to Z/2 + Z + Z
Defined on 3 generators
Relations:
    2*G.1 = 0
[ (1/4*(3*K.1^2 + 48) : 1/2*(K.1^2 - 4*K.1 + 12) : 1), (1/4*(19*K.1^2 + 4*K.1 +
    240) : 1/3*(-103*K.1^2 - 40*K.1 - 1246) : 1), (1/273612*(-29047*K.1^2 -
    115492*K.1 + 548144) : 1/10328853*(1076491*K.1^2 - 22819136*K.1 + 22265518)
: 1) ]
supp(R) = [ 2, 3, 5, 13 ]
Verify Saturation= true
Solutions for twist  1  =  { (1 : 0) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/9*(-32*$.1^2 + 112*$.1 - 512))
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 2 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (12*K.1^2 + 192 : -112*K.1^2 - 224*K.1 - 2016 : 1), (1/9*(-32*K.1^2 + 112*K.1
    - 512) : 1/9*(-224*K.1^2 - 448*K.1 + 5376) : 1) ]
supp(R) = [ 2, 3 ]
Verify Saturation= true
Solutions for twist  2  =  { (2 : 1) }
[
    1,
    1/3*(7*K.1^2 + 28*K.1 + 112)
]
{ (2 : 1), (1 : 0) }
*/






////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////
////////////////////////////////////////////////////



//N=390

_<x>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);

f:=(x^2-x+1)*(x^4+5*x^3-8*x^2+5*x+1);

X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (1 : 1), (1 : 0), (0 : 1) }

//We computed the deltas. We get

A<theta>:=quo<PolynomialRing(Rationals())| f>;
deltas:=[1,-theta,1-theta];
pdeltas:=[P1![1,0],P1![0,1],P1![1,1]];

//First we try the case K=Rationals()
K:=Rationals();
Ff:=Factorization(f);
g:=Ff[2][1];
MyEllipticChabauty(g,deltas,uXrat);
/*
[ 1 ]
[
    { (1 : 1), (1 : 0), (0 : 1) }
]

Torsion Subgroup = Z/2
Analytic rank = 1
     ==> Rank(E) = 1

Rank for twist= 1 = [ 1, 1 ]
[]
{}
*/
//No point
//Note however that all rational points of X lift 
//to a rational point of the trivial cover, since 
//there is only one twist.

//We tried to go to the degree 2 extension and Chabauty was not succesfull
//We tried to go to the degree 8 extension and it took too long 


/*
We try a diferent idea: the 2-covering over the rationals is equal to 
r^2=(x^2-x+1)
s^2=(x^4+5*x^3-8*x^2+5*x+1)

Parametrizing the first equation we get 

x=(2*t-1)/(t^2-1)

we get the second equation is (with y=(t^4 - 2*t^2 + 1)*s)

y^2=(t^8 + 10*t^7 - 41*t^6 + 42*t^5 + 33*t^4 - 76*t^3 + 44*t^2 - 16*t + 4);

So any point of X comes from two points of this last equation. We apply now 
the same ideas here (note that this hyperelliptic curve of genus 3 has 
jacobian of rank 3, so usual Chabauty does not applies. 

We try where this polynomial factorizes: Adjoining one root we get 4 roots. Several 
degree 2 extensions appear where we have a factorization.
*/


F<t>:=PolynomialRing(Rationals());
f:=t^8 + 10*t^7 - 41*t^6 + 42*t^5 + 33*t^4 - 76*t^3 + 44*t^2 - 
16*t + 4;
K:=NumberField(f);
S:=Subfields(K);
S2:=[L[1]: L in S | Degree(L[1]) eq 2]; 
S2;
/*
[
    Number Field with defining polynomial t^2 + 36*t + 4 over the Rational
    Field,
    Number Field with defining polynomial t^2 - 68*t + 324 over the Rational
    Field,
    Number Field with defining polynomial t^2 - 9*t + 4 over the Rational Field
]
*/


_<t>:=PolynomialRing(Rationals());
P1:=ProjectiveSpace(Rationals(),1);

f:=t^8 + 10*t^7 - 41*t^6 + 42*t^5 + 33*t^4 - 76*t^3 + 44*t^2 - 16*t + 4;

X:=HyperellipticCurve(f);
Xrat:=Points(X: Bound:=10000);
uX:=map<X->P1|[X.1,X.3]>;
uXrat:={uX(P):P in Xrat};

print "Set of x-coordinates:", uXrat;
//Set of x-coordinates: { (1 : 1), (2 : 1), (1 : 0), (-1 : 1), (0 : 1), (1/2 : 1)}

//We compute the productive deltas 

Hk,AtoHk:=TwoCoverDescent(X);
A<theta>:=Domain(AtoHk);
deltas:=[1,2-theta,1-theta,-1-theta,-theta,1/2-theta];
{AtoHk(delta): delta in deltas} eq Hk;
//true 
//all deltas are productive



A<theta>:=quo<PolynomialRing(Rationals())|f>;
deltas:=[1,2-theta,1-theta,-1-theta,-theta,1/2-theta];

K:=NumberField(t^2 + 36*t + 4);
Ff:=Factorization(ChangeRing(f,K));
Ff;
g:=Ff[1][1];

MyEllipticChabauty(g,deltas,uXrat);

/*
[
    1,
    18,
    9/2*K.1,
    K.1
]
[
    { (1 : 1), (1 : 0) },
    { (2 : 1) },
    { (-1 : 1), (1/2 : 1) },
    { (0 : 1) }
]


Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 26*$.1 + 64)
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 1 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (13/8*K.1 : 13/4*K.1 : 1), (1/8*(13*K.1 + 32) : 1/4*(13*K.1 + 32) : 1) ]
supp(R) = [ 2, 3, 5 ]
Solutions for twist  1  =  { (1 : 1), (1 : 0) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 1
After 2-descent:
    0 <= Rank(E) <= 0
    Sha(E)[2] is trivial

Rank for twist= 2 = [ 0, 0 ]
Solutions for twist  2  =  { (2 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 2
New point of infinite order (x = 1/2*(-13*$.1 - 436))
After 2-descent:
    1 <= Rank(E) <= 1
    Sha(E)[2] is trivial
(Searched up to height 16 on the 2-coverings.)

Rank for twist= 3 = [ 1, 1 ]
Abelian Group isomorphic to Z/2 + Z
Defined on 2 generators
Relations:
    2*G.1 = 0
[ (1/2*(-13*K.1 - 468) : -26*K.1 - 936 : 1), (1/2*(-13*K.1 - 436) : -18*K.1 -
    440 : 1) ]
supp(R) = [ 2, 3, 5 ]
Solutions for twist  3  =  { (-1 : 1), (1/2 : 1) }

Torsion Subgroup = Z/2
The 2-Selmer group has rank 1
After 2-descent:
    0 <= Rank(E) <= 0
    Sha(E)[2] is trivial

Rank for twist= 4 = [ 0, 0 ]
Solutions for twist  4  =  { (0 : 1) }
[
    1,
    18,
    9/2*K.1,
    K.1
]
{ (2 : 1), (1 : 1), (-1 : 1), (1/2 : 1), (0 : 1), (1 : 0) }



*/

//Hence we computed all the points of this curve, so of the original curve. 

