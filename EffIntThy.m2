newPackage( "EffIntThy",
    Version =>"0.2",
    Date => "Jan 3, 2018",
    Authors => {
        {Name => "Martin Helmer",
         Email => "martin.helmer@berkeley.edu",
         HomePage => "http://martin-helmer.com"},
        {Name => "Corey Harris",
         Email => "Corey.Harris@mis.mpg.de",
         HomePage => "http://coreyharris.name"}
    },
    Headline => "Computes s(X,Y) in  A*(P^n1x...xP^nm)",
    PackageImports => {"NumericalAlgebraicGeometry"},
    DebuggingMode => false,
    Reload => true
);

export {
   "ChowRing",
   "chowRing",
   "MultiProjCoordRing",
   "isMultiHomogeneous",
   "Segre",
   "projectiveDegree",
   "projectiveDegrees",
   "makeMultiHom",
   "HomMethod",
   "ProjDegMethod",
   "SloppinessLevel",
   "Sparsity",
   "CompMethod",
   "eXYmult",
   "chowClass"
}

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

IntersectionRing = new Type of MutableHashTable
globalAssignment IntersectionRing
intersectionRing = method(TypicalValue => IntersectionRing)
intersectionRing(Ring,ZZ) := (R,ambientdim) -> (
    basisR := flatten entries sort basis R;
    pointClassIndex := position(basisR, w -> sum(flatten exponents(w))==ambientdim);
    codim1basis := select(basisR, w -> sum(degree w)==1 );
    return new IntersectionRing from {
        global ring => R,
        global pointClass => basisR#pointClassIndex,
        global codim1Basis => codim1basis,
        global basis => basisR,
        global ambientDim => ambientdim
    }
)

ring IntersectionRing := R -> ( R.ring )
pointClass = R -> ( R.pointClass )
codim1Basis = R -> ( R.codim1Basis )
ambientDim = R -> ( R.ambientDim )
basis IntersectionRing := R -> ( R.basis )

Scheme = new Type of MutableHashTable
globalAssignment Scheme
toString Scheme := net Scheme := X -> (
    if hasAttribute(X,ReverseDictionary) then toString getAttribute(X,ReverseDictionary)
    else "a scheme")
Scheme#{Standard,AfterPrint} = X -> (
    << concatenate(interpreterDepth:"o") << lineNumber << " : "
    -- << "a projective scheme in PP^" << dim(X.AmbientSpace) << " defined by " << X.Ideal << endl;
)

scheme = method(TypicalValue => Scheme, Options => {})
scheme Ideal :=  opts -> I -> (
    R := ring I;
    A := ChowRing(R);
    return new Scheme from {
        global ideal => I,
        global ring => R,
        global coefficientRing => coefficientRing ring I,
        global chowRing => intersectionRing(A, numgens(R)-length unique degrees R)
    }
)
scheme(Ideal,IntersectionRing) :=  opts -> (I,intRing) -> (
    R := ring I;
    return new Scheme from {
        global ideal => I,
        global ring => R,
        global coefficientRing => coefficientRing ring I,
        global chowRing => intRing
    }
)

ideal Scheme := X -> ( X.ideal )
ring Scheme := X -> ( X.ring )
codim Scheme := {} >> opts -> X -> (
    if not X.?codim then ( X.codim = codim ideal leadTerm gb(X) );
    return X.codim
)
gb Scheme := opts -> X -> (
    if not X.?gb then ( X.gb = groebnerBasis(ideal X) );
    return X.gb
)
dim Scheme := X -> (
    if not X.?dim then (
        X.dim = numgens(ring X) - #(unique degrees ring X) - codim(X);
    );
    return X.dim
)

projectiveDegree = method(TypicalValue => RingElement,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4,Verbose=>false});
projectiveDegree (Ideal,Ideal,RingElement) :=opts-> (IX,IY,w) -> (
    Y := scheme(IY);
    X := scheme(IX+IY);
    R := ring Y;
    Y.chowRing = intersectionRing(ring w, numgens(R)-length unique degrees R);
    X.chowRing = Y.chowRing;
    X.equations = IX;

    return projectiveDegree(X,Y,w)
);
projectiveDegree(Scheme,Scheme,RingElement) := opts -> (sX,sY,w) -> (
    A := sX.chowRing;
    X := ideal sX;
    Y := ideal sY;
    R:=ring X;
    kk:=coefficientRing(R);
    Ls:=0;
    wDims:=flatten exponents(A.pointClass//w);
    wTotalDim := sum wDims;
    for i from 0 to length(wDims)-1 do (
        if wDims_i!=0 then (
            Ls=Ls+sum(wDims_i,j->ideal(random(OneAti(degreeLength R,i),R)));
        );
    );
    Wg:=flatten entries gens (makeMultiHom(X,sY)+Ls);
    G:=ideal(for j from 1 to dim(sY)-wTotalDim list sum(Wg,g->random(kk)*g));
    irrelevantIdealsHash := partition(degree, gens R);
    irrelevantIdeals := values irrelevantIdealsHash / ideal;
    LA := sum(irrelevantIdeals, p -> sub(ideal(1-sum(numgens(p),i->random(kk)*p_i)),R));

    pd := 0;
    if opts.ProjDegMethod=="Sat" then (
        pd = degree saturate(Y+Ls+G+LA,X)
    ) else if(opts.ProjDegMethod=="NAG") then (
        Sys:=flatten entries gens(Y+Ls+G+LA);
        sols:=solveSystem Sys;
        Fsys:=flatten entries gens (X+Y);
        badsols:=0;
        for s in sols do (
            badSol:=true;
            for f in Fsys do (
                if sub(f,matrix{coordinates s})>1e-10 then badSol=false;
            );
            if badSol==true then badsols=badsols+1;
        );
        pd = #sols-badsols
    ) else (
        --Default Method
        S:=kk(monoid[gens R,getSymbol "t"]);
        t := last gens S;
        EqT:=ideal( 1-t*sum((numgens X),j->(random(kk)*substitute(X_j,S))));
        ZeroDimGB:=groebnerBasis(sub(Y+Ls+G+LA,S)+EqT, Strategy=>"F4");
        pd = numColumns basis(cokernel leadTerm ZeroDimGB);
    );
    return pd;
);

projectiveDegrees = method(TypicalValue => List,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4,Verbose=>false});
projectiveDegrees(Ideal,Ideal) := opts -> (I,J) -> (
    R :=ring J;
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(ChowRing R,n);
    Y := scheme(J,IA);
    X := scheme(I+J,IA);
    X.equations = I;
    return projectiveDegrees(X,Y)    
)
projectiveDegrees (Scheme,Scheme) := opts -> (X,Y) -> (
    A := X.chowRing;
    projectiveDegreesList := {};
    for i from 0 to dim(X) do (
        for w in A.basis do (
            if sum(flatten exponents(w))==A.ambientDim-i then (
                pd:=projectiveDegree(X, Y, w,opts);
                projectiveDegreesList = append(projectiveDegreesList,pd*w);
            );
        );
    );
    return projectiveDegreesList
)

eXYmult=method(TypicalValue=>ZZ,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4,Verbose=>false});
eXYmult (Ideal,Ideal) := opts->(I1,I2) -> (
    if opts.Verbose then print "eXYmult(I,J) computes e_XY where X is the top equidimensional component of V(I) and Y=V(J) (Y is assumed to be irreducible)";
    Iinfo:=new MutableHashTable;
    A:=ChowRing(ring(I2));
    clX:=chowClass(I1+I2,A,CompMethod=>"multidegree");
    seg:= Segre(I1,I2,A,opts);
    mons:=flatten entries monomials clX;
    segMons:=sum(for m in mons list m*seg_(m));
    if opts.Verbose then <<"[X]= "<<clX<<" these monomials in Segre class= "<<segMons<<endl;
    return lift(segMons//clX,ZZ);
);

chowClass=method(TypicalValue=>ZZ,Options => {CompMethod=>"multidegree"});
chowClass Scheme := opts -> X -> (
    -- if not X.?chowClass then X.chowClass = chowClass(ideal X,ring(X.chowRing));
    if X.?chowClass then return X.chowClass;
    R := ring X;
    IA := X.chowRing;
    classI:=0;
    if opts.CompMethod=="multidegree" then (
        md:=multidegree (ideal X);
        classI=sub(md,matrix{gens ring IA});
    ) else (
        irrelevantIdealsHash := partition(degree, gens R);
        irrelevantIdeals := values irrelevantIdealsHash / ideal;
        ZeroDimGB:=0;
        kk:=coefficientRing(R);
        LA := sum(irrelevantIdeals, p -> sub(ideal(1-sum(numgens(p),i->random(kk)*p_i)),R));
        c := for w in IA.basis list if sum(flatten(exponents(w)))==codim X then w else continue;
        for w in c do (
            Ls:=0;
            wDims:=flatten exponents(IA.pointClass//w);
            for i from 0 to length(wDims)-1 do (
                if wDims_i!=0 then (
                    Ls=Ls+sum(wDims_i,j->ideal(random(OneAti(degreeLength R,i),R)));
                );
            );
            ZeroDimGB=ideal groebnerBasis(ideal(gb X)+Ls+LA, Strategy=>"F4");
            classI=classI+(numColumns basis(cokernel leadTerm ZeroDimGB))*w;
        );
    );
    X.chowClass = classI;
    return X.chowClass
);
chowClass (Ideal,Ring) := opts -> (I,A) -> (
    return sub(multidegree I, matrix{ gens A })
)
chowClass (Ideal) := opts -> (I) -> (
    A:=ChowRing(ring I);
    return sub(multidegree I, matrix{ gens A });
);

isMultiHomogeneous=method(TypicalValue=>Boolean);
isMultiHomogeneous Ideal:=I->(
    Igens:=flatten entries gens(I);
    d:=0;
    fmons:=0;
    for f in Igens do (
        fmons=flatten entries monomials(f);
        if length(fmons)>1 then (
            d=degree(first(fmons));
            for mon in fmons do (
                if degree(mon)!=d then (
                    <<"Input term below is not homogeneous with respect to the grading"<<endl;
                    <<f<<endl;
                    return false;
                );
            );
        );
    );
return true;
);
isMultiHomogeneous RingElement:=f->(
    return isMultiHomogeneous(ideal(f));
);

makeMultiHom=method(TypicalValue=>Ideal);
--TODO Replace this (Ideal,Ideal,ZZ) version with a wrapper for the Hash input version below
makeMultiHom (Ideal,Ideal,ZZ):=(K,J,dimY)->(
    I:=K+J;
    R:=ring I;
    n:=numgens(R)-length(unique degrees R);
    kk:=coefficientRing R;
    gensI:= delete(0_R,flatten sort entries gens K);
    homGens:={};
    maxDegs := for d in transpose degrees I list max d;
    curIrel:=0;
    degDif:=0;
    tempfGens:=0;

    irrelevantIdealsHash := partition(degree, gens R);

    for f in gensI do (
        if degree(f)==maxDegs then (
            homGens=append(homGens,f);
        ) else (
            degDif=maxDegs-degree(f);
            tempfGens=ideal(f);
            for i from 0 to #degDif-1 do (
                curIrel=irrelevantIdealsHash#(OneAti(degreeLength R,i));
                tempfGens=tempfGens*ideal(for g in curIrel list g^(degDif_i));
            );
        homGens=join(homGens,flatten entries gens tempfGens);
        );
    );
    return ideal for j from 0 to dimY list sum(homGens,l->l*random(kk)*random(0,4));
    --return ideal homGens;
);
makeMultiHom (Ideal,Scheme):=(eqsX,Y)->(
    J := ideal Y;
    I:=eqsX+J;
    R:=ring I;
    n:=numgens(R)-length(unique degrees R);
    kk:=coefficientRing R;
    gensI:= delete(0_R,flatten sort entries gens eqsX);
    homGens:={};
    maxDegs := for d in transpose degrees I list max d;
    curIrel:=0;
    degDif:=0;
    tempfGens:=0;

    irrelevantIdealsHash := partition(degree, gens R);

    for f in gensI do (
        if degree(f)==maxDegs then (
            homGens=append(homGens,f);
        ) else (
            degDif=maxDegs-degree(f);
            tempfGens=ideal(f);
            for i from 0 to #degDif-1 do (
                curIrel=irrelevantIdealsHash#(OneAti(degreeLength R,i));
                tempfGens=tempfGens*ideal(for g in curIrel list g^(degDif_i));
            );
        homGens=join(homGens,flatten entries gens tempfGens);
        );
    );
    return ideal for j from 0 to dim(Y) list sum(homGens,l->l*random(kk)*random(0,4));
    --return ideal homGens;
);

MultiProjCoordRing=method(TypicalValue=>Ring);
MultiProjCoordRing (Symbol,List):=(x,l)->(
    kk:=ZZ/32749;
    return MultiProjCoordRing(kk,x,l);
);
MultiProjCoordRing (Ring,List):=(kk,l)->(
    x:=getSymbol "x";
    return MultiProjCoordRing(kk,x,l);
);
MultiProjCoordRing (List):=(l)->(
    x:=getSymbol "x";
    kk:=ZZ/32749;
    return MultiProjCoordRing(kk,x,l);
);
MultiProjCoordRing (Ring, Symbol,List):=(kk,x,l)->(
    if not isField(kk) then (
        <<"The coefficent ring must be a field, using the default field kk=ZZ/32749"<<endl;
        kk=ZZ/32749;
    );
    m:=length(l);
    numVars:=sum(l)+m;
    degs:={};
    ind:=0;
    for n in l do (
        for i from 0 to n do (
            degs=append(degs,OneAti(m,ind));
        );
        ind=ind+1;
    );
    return kk(monoid[vars(0..numVars-1),Degrees=>degs]);
);

ChowRing=method(TypicalValue=>QuotientRing);
ChowRing (Ring):=(R)->(
    h := getSymbol "h";
    return ChowRing(R,h);
);
ChowRing (Ring,Symbol):=(R,h)->(
    Rdegs:=degrees R;
    ChDegs:=unique Rdegs;
    m:=length ChDegs;
    C:= ZZ(monoid[h_1..h_m, Degrees=>ChDegs]);
    K:={};
    ns:={};
    temp:=0;
    for d in ChDegs do (
        temp=0;
        for a in Rdegs do (
            if d==a then temp=temp+1;
        );
        ns=append(ns,temp);
    );

    for i from 0 to length(ChDegs)-1 do (
        K=append(K,C_(i)^(ns_i));
    );
    K=substitute(ideal K,C);
    A:=C/K;
    return A;
);

Segre=method(TypicalValue => RingElement,Options => {HomMethod=>2,ProjDegMethod=>"AdjT",SloppinessLevel=>1,Sparsity=>4,Verbose=>false});
Segre (Ideal,Ideal) :=opts-> (I1,I2) -> (
    --print "start segre wrapper";
    A:=ChowRing(ring(I2));
    return Segre(I1,I2,A,opts);
);
Segre (Ideal,Ideal,QuotientRing) :=opts->(X,Y,A) -> (
    if not isMultiHomogeneous(X) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHomogeneous(Y) then (print "the second ideal is not multi-homogenous, please correct this"; return 0;);

    R :=ring Y;
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(A,n);
    sY := scheme(Y,IA);
    sX := scheme(X+Y,IA);
    sX.equations = X;

    if opts.ProjDegMethod=="NAG" and char(coefficientRing R)!=0 then (print "Use QQ for NAG"; return 0;);

    --find the max multidegree, write it as a class alpha
    maxDegs := for d in transpose degrees (X+Y) list max d;
    alpha := sum(length IA.codim1Basis,i->(basis(OneAti(degreeLength R,i),A))_0_0*maxDegs_i);
    if opts.Verbose then <<"[Y]= "<<chowClass(sY)<<", alpha= "<<alpha<<endl;

    -- All the hard work is hidden in the next line
    projectiveDegreesList := projectiveDegrees(sX,sY);
    if opts.Verbose then <<"Projective degrees= "<<projectiveDegreesList<<endl;

    --build Segre class recursivly from Proj Degs
    segreClass:=0_A;
    RHS:=sum(0..dim sX,i->alpha^(dim sY-i)*chowClass(sY)) - sum(projectiveDegreesList);
    basisByCodim := partition(i -> sum(flatten exponents i), IA.basis);
    for i from 0 to dim sX do (
        for w in basisByCodim#(codim(sX)+i) do (
            L:=(IA.pointClass//w);
            C:=RHS_(w)-(L*(1+alpha)^(dim(sY)-sum(flatten exponents(L)))*segreClass)_(IA.pointClass);
            segreClass=segreClass+C*w;
            --<<"w= "<<w<<", SegClass= "<<SegClass<<" coeff= "<<(1+alpha)^(dimY-sum(flatten(exponents(temp9))))<<endl;
        );
    );
    if opts.Verbose then <<"s(X,Y)= "<<segreClass<<endl;
    return segreClass;
);

----------------------------
-- utility functions
----------------------------

OneAti=(dl,i)->(
    vec:={};
    for j from 0 to dl-1 do (
        if j==i then vec=append(vec,1) else vec=append(vec,0);
    );
    return vec;
)


beginDocumentation()
multidoc ///

///


TEST ///
-- union of coordinate axes in PP3 (diagonal)
{*
restart
needsPackage "EffIntThy"
*}
R = MultiProjCoordRing({3,3})
x = gens(R)
D = minors(2,matrix{{x_0..x_3},{x_4..x_7}})
X = ideal(x_0*x_1,x_1*x_2,x_0*x_2)
A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^4,b^4)
s = Segre(X,D,A,Verbose=>true)
assert(s == 3*(a^3*b^2+a^2*b^3)-10*(a^3*b^3))
///

TEST ///
{*
restart
needsPackage "EffIntThy"
*}
R=MultiProjCoordRing({6})
x=gens(R)
degrees R
I=ideal(random(2,R),x_0^4-x_1*x_3^3-x_4*x_5^3)
J=ideal(x_0*x_2-x_4*x_5)
chowClass(J,CompMethod=>"prob")
-- having this here breaks the test (!?).  Separating for now...
-- A = ZZ[h]/(h^7)
-- assert(Segre(I,J,A,Verbose=>true)==16*h^3-96*h^4+448*h^5-1920*h^6)
assert(eXYmult(I,J,Verbose=>true)==1)
///

TEST ///
-- union of coordinate axes in PP3 (diagonal)
{*
restart
needsPackage "EffIntThy"
*}
R = MultiProjCoordRing({3,3})
x = gens(R)
D = minors(2,matrix{{x_0..x_3},{x_4..x_7}})
X = ideal(x_0*x_1,x_1*x_2,x_0*x_2)
pds = projectiveDegrees(X,D,Verbose=>true)
A = ring first pds
(a,b) = toSequence gens A
l = {10*a^3*b^3, 6*a^2*b^3, 6*a^3*b^2, 3*a*b^3, 3*a^2*b^2, 3*a^3*b}
pds = pds  / (i -> sub(i,A))
assert(sort(pds)==sort(l))
///

TEST ///
{*
restart
needsPackage "EffIntThy"
*}
R=MultiProjCoordRing({6})
x=gens(R)
degrees R
I=ideal(random(2,R),x_0^4-x_1*x_3^3-x_4*x_5^3)
J=ideal(x_0*x_2-x_4*x_5)
chowClass(J,CompMethod=>"prob")
A = ZZ[h]/(h^7)
assert(Segre(I,J,A,Verbose=>true)==16*h^3-96*h^4+448*h^5-1920*h^6)
///

TEST ///
{*
restart
needsPackage "EffIntThy"
*}
R = ZZ/32003[x,y,z,w];
I = ideal(-z^2+y*w,-y*z+x*w)
J = ideal(-z^3+2*y*z*w-x*w^2,-y^2+x*z)
assert(eXYmult(I,J)==2)
///

TEST ///
{*
restart
needsPackage "EffIntThy"
*}
-- Cx is a hyperplane section on a smooth quadric surface
-- embedded in the diagonal of P3xP3
R=MultiProjCoordRing({3,3})
x=(gens(R))_{0..3}
y=(gens(R))_{4..7}
Qx = ideal (x#0*x#1 - x#2*x#3)
Qy=sub(Qx,matrix{join(y,for i from 4 to 7 list 0)})
D = minors(2,matrix{x,y})
I=ideal(Qx,Qy,D) --Q in the diagional
Cx=ideal random({1,0},R)
A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^4,b^4)
s=Segre(Cx,I,A,Verbose=>true)
assert(s == 2*(a^3*b^2+a^2*b^3-a^3*b^3))
///

TEST ///
{*
restart
needsPackage "EffIntThy"
*}
R=MultiProjCoordRing({2,1});
x=(gens R)_{0..2};
y=(gens R)_{3..4};
I = ideal (x_0,x_1);  -- choosing a simple point to make things easier
B=ideal(y_0*I_1-y_1*I_0); ---blow up of this point...
E=B+ideal (x_0,x_1);
A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^3,b^2)
s=Segre(E,B,A,Verbose=>true)
assert(s == a^2 + a^2*b)
///

end

restart
check "EffIntThy"

restart
needsPackage "EffIntThy"
kk=ZZ/32749
R = MultiProjCoordRing(kk,{2,3})
x=(gens R)_{0..2}
y=(gens R)_{3..6}
I=ideal(x_0^2*x_1*y_1^2-x_0^3*y_0*y_3)
J=ideal(x_1^2*x_0*y_3^2-x_0^3*y_2*y_0-x_0^3*y_0^2)
time seg=Segre(I,J)

restart
needsPackage "EffIntThy"
kk=ZZ/32749
R = kk[x,y,z,t]
PP3xPP3 = MultiProjCoordRing(kk,{3,3})
m1 = map(PP3xPP3,R,take(gens PP3xPP3,4))
m2 = map(PP3xPP3,R,drop(gens PP3xPP3,4))
f = ideal "x(x2-2xy+zt) + y(x2-3yt+z2+3t2-3tz+xy)"
h = ideal "x(x2-7y2-zt) + y(3x2-5yt)"
g = ideal "x(23xy-34z2-17yt+t2) + y(x2+y2+z2+xy+zt)"
X = m1(f+g)
Y = m2(h+g)
D = minors(2,matrix{take(gens PP3xPP3,4),drop(gens PP3xPP3,4)})
-- this example takes 30secs or so... (07.01.18)
time Segre(D,X+Y,HomMethod=>2)
