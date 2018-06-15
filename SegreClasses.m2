newPackage( "SegreClasses",
    Version =>"1.01",
    Date => "June 15, 2018",
    Authors => {
        {Name => "Martin Helmer",
         Email => "m.helmer@math.ku.dk",
         HomePage => "http://martin-helmer.com"},
        {Name => "Corey Harris",
         Email => "Corey.Harris@mis.mpg.de",
         HomePage => "http://coreyharris.name"}
    },
    Headline => "Computes s(X,Y) in  A*(P^n1x...xP^nm)",
    PackageImports => {"CharacteristicClasses"},
    DebuggingMode => false,
    Reload => true
);

export {
   "chowClass",
   "intersectionProduct",
   "isMultiHom",
   "makeMultiHom",
   "makeChowRing",
   "makeProductRing",
   "multiplicity",
   "projectiveDegree",
   "projectiveDegrees",
   "containedInSingularLocus",
   "segre",
   "segreDimX",
   "isComponentContained"
}

chowRing = getSymbol "chowRing";
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
)

scheme = method(TypicalValue => Scheme, Options => {})
scheme Ideal :=  opts -> I -> (
    R := ring I;
    A := makeChowRing(R);
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
saturate Scheme :=opts ->  X -> (
    if not X.?saturate then (
        X.saturate = saturate(ideal X,product (values partition(degree, gens(ring(X))) / ideal));
    );
    return X.saturate;
)
containedInSingularLocus = method(TypicalValue => Boolean,Options => {Verbose=>false});
containedInSingularLocus (Ideal,Ideal) :=opts-> (IX,IY) -> (
    eXY:=multiplicity(IX,IY);
    if opts.Verbose then <<"e_XY= "<<eXY<<endl;
    return eXY>1;
);
isComponentContained = method(TypicalValue => Boolean,Options => {Verbose=>false});
isComponentContained (Ideal,Ideal) :=opts-> (IX,IY) -> (
    if not isMultiHom(IY) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    R:=ring IY;
    A:=makeChowRing(R);
    kk:=coefficientRing(R);
    Y:=makeMultiHom (IY,ideal 0_R);
    X:=makeMultiHom (IX,ideal 0_(ring IX));
    Theta:=sub(ideal(sum((numgens X),j->random(kk)*X_j)),R);
    F:=ideal sum((numgens Y),j->random(kk)*Y_j);
    Z:=Theta*F;
    s1:=segreDimX(X,Z,A);
    if opts.Verbose then <<"{Lambda(X,Z)}_dim(X)= "<<s1<<endl;
    s2:=segreDimX(X,Theta,A);
    if opts.Verbose then <<"{Lambda(X,Theta)}_dim(X)= "<<s2<<endl;
    return s1!=s2;
);
projectiveDegree = method(TypicalValue => RingElement,Options => {Verbose=>false});
projectiveDegree (Ideal,Ideal,RingElement) :=opts-> (IX,IY,w) -> (
    Y := scheme(IY);
    X := scheme(IX+IY);
    R := ring Y;
    Y.chowRing = intersectionRing(ring w, numgens(R)-length unique degrees R);
    X.chowRing = Y.chowRing;
    --X.equations = IX;

    return projectiveDegree(X,Y,w);
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
    --TODO: Cache makeMultiHom(X,sY), maybe in sX or sY?
    Wg:=flatten entries gens (makeMultiHom(X,sY)+Ls);
    G:=ideal(for j from 1 to dim(sY)-wTotalDim list sum(Wg,g->random(kk)*g));
    irrelevantIdealsHash := partition(degree, gens R);
    irrelevantIdeals := values irrelevantIdealsHash / ideal;
    LA := sum(irrelevantIdeals, p -> sub(ideal(1-sum(numgens(p),i->random(kk)*p_i)),R));
    pd := 0;
    S:=kk(monoid[gens R,getSymbol "t"]);
    t := last gens S;
    EqT:=ideal( 1-t*sum((numgens X),j->(random(kk)*substitute(X_j,S))));
    ZeroDimGB:=groebnerBasis(sub(Y+Ls+G+LA,S)+EqT, Strategy=>"F4");
    pd = numColumns basis(cokernel leadTerm ZeroDimGB);
    return pd;
);

projectiveDegrees = method(TypicalValue => List,Options => {Verbose=>false});
projectiveDegrees(Ideal,Ideal,QuotientRing) := opts -> (I,J,A) -> (
    if not isMultiHom(I) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHom(J) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    R :=ring J;
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(A,n);
    Y := scheme(J,IA);
    X := scheme(I+J,IA);
    --X.equations = I;
    return projectiveDegrees(X,Y);
)

projectiveDegrees(Ideal,Ideal) := opts -> (I,J) -> (
    R :=ring J;
    if not isMultiHom(I) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHom(J) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(makeChowRing R,n);
    Y := scheme(J,IA);
    X := scheme(I+J,IA);
    --X.equations = I;
    return projectiveDegrees(X,Y);
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
    return projectiveDegreesList;
)
segreDimX = method(TypicalValue => List,Options => {Verbose=>false});
segreDimX (Ideal,Ideal,QuotientRing) := opts -> (X,Y,A) -> (
    if not isMultiHom(X) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHom(Y) then (print "the second ideal is not multi-homogenous, please correct this"; return 0;);
    R :=ring Y;
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(A,n);
    sY := scheme(Y,IA);
    sX := scheme(X+Y,IA);
    segreClass:=0_A;
    basisByCodim := partition(i -> sum(flatten exponents i), IA.basis);
    projectiveDegreesList := {};
    for w in IA.basis do (
	if sum(flatten exponents(w))==IA.ambientDim-dim(sX) then (
	    pd:=projectiveDegree(sX, sY, w);
	    projectiveDegreesList = append(projectiveDegreesList,pd*w);
	    );
	);
    --print projectiveDegreesList;
    --find the max multidegree, write it as a class alpha
    i:= codim(sX);
    maxDegs := for d in transpose degrees (X+Y) list max d;
    alpha := sum(length IA.codim1Basis,i->(basis(OneAti(degreeLength R,i),A))_0_0*maxDegs_i);
    RHS:=sum(0..dim sX,i->alpha^(dim sY-i)*chowClass(sY)) - sum(projectiveDegreesList);
    for w in basisByCodim#(i) do (
	L:=(IA.pointClass//w);
        C:=RHS_(w)-(L*(1+alpha)^(dim(sY)-sum(flatten exponents(L)))*segreClass)_(IA.pointClass);
        segreClass=segreClass+C*w;
        );
    --print segreClass;
    return segreClass;
);

multiplicity=method(TypicalValue=>ZZ,Options => {Verbose=>false});
--TODO Add multiplicity (Scheme,Scheme), make this a wrapper
multiplicity (Ideal,Ideal) := opts->(I1,I2) -> (
    if opts.Verbose then print "multiplicity(I,J) computes e_XY where X is the top equidimensional component of V(I) and Y=V(J) (Y is assumed to be irreducible)";
    if not isMultiHom(I1) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHom(I2) then (print "the second ideal is not multi-homogenous, please correct this"; return 0;);
    R :=ring I2;
    A:=makeChowRing(R);
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(A,n);
    sY := scheme(I2,IA);
    sX := scheme(I1+I2,IA);
    clX:=chowClass(I1+I2,A,Strategy=>"multidegree");
    ha:=first flatten entries monomials clX;
    ba:=clX_(ha);
    ga:=projectiveDegree(sX,sY,ha);
            --find the max multidegree, write it as a class alpha
    maxDegs := for d in transpose degrees (I1+I2) list max d;
    alpha := sum(length IA.codim1Basis,i->(basis(OneAti(degreeLength R,i),A))_0_0*maxDegs_i);
    Lambda:=alpha^(dim(sY)-dim(sX))*chowClass(I2,A);
    ca:=Lambda_(ha);
    eXY:=(ca-ga)/ba;
    --<<"g_a= "<<ga<<", Lambda_a= "<<(ca-ga)<<endl; 
    return eXY;
);

chowClass=method(TypicalValue=>ZZ,Options => {Strategy=>"multidegree"});
chowClass Scheme := opts -> X -> (
    -- if not X.?chowClass then X.chowClass = chowClass(ideal X,ring(X.chowRing));
    if X.?chowClass then return X.chowClass;
    R := ring X;
    IA := X.chowRing;
    classI:=0;
    if opts.Strategy=="multidegree" then (
        md:=multidegree saturate X;
        classI=sub(md,matrix{gens ring IA});
	) 
    else(
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
            ZeroDimGB=ideal groebnerBasis(saturate(X)+Ls+LA, Strategy=>"F4");
            classI=classI+(numColumns basis(cokernel leadTerm ZeroDimGB))*w;
        );
    );
    X.chowClass = classI;
    return X.chowClass;
);
chowClass (Ideal,Ring) := opts -> (I,A) -> (
    if not isMultiHom(I) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    R:=ring I;
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(A,n);
    return chowClass(scheme(I,IA),opts);
    --return sub(multidegree I, matrix{ gens A })
)
chowClass (Ideal) := opts -> (I) -> (
    if not isMultiHom(I) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    return chowClass(scheme(I),opts);
    --A:=makeChowRing(ring I);
    --return sub(multidegree I, matrix{ gens A });
);

isMultiHom=method(TypicalValue=>Boolean);
isMultiHom Ideal:=I->(
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
isMultiHom RingElement:=f->(
    return isMultiHom(ideal(f));
);

makeMultiHom=method(TypicalValue=>Ideal);
makeMultiHom (Ideal,Ideal):=(I,J) -> (
    makeMultiHom(I, scheme(J))
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

makeProductRing=method(TypicalValue=>Ring);
makeProductRing (Symbol,List):=(x,l)->(
    kk:=ZZ/32749;
    return makeProductRing(kk,x,l);
);
makeProductRing (Ring,List):=(kk,l)->(
    x:=getSymbol "x";
    return makeProductRing(kk,x,l);
);
makeProductRing (List):=(l)->(
    x:=getSymbol "x";
    kk:=ZZ/32749;
    return makeProductRing(kk,x,l);
);
makeProductRing (Ring, Symbol,List):=(kk,x,l)->(
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

makeChowRing=method(TypicalValue=>QuotientRing);
makeChowRing (Ring):=(R)->(
    h := getSymbol "H";
    return makeChowRing(R,h);
);
makeChowRing (Ring,Symbol):=(R,h)->(
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

segre=method(TypicalValue => RingElement,Options => {Verbose=>false});
segre (Ideal,Ideal) :=opts-> (I1,I2) -> (
    A:=makeChowRing(ring(I2));
    return segre(I1,I2,A,opts);
);
segre (Ideal,Ideal,QuotientRing) :=opts->(X,Y,A) -> (
    if not isMultiHom(X) then (print "the first ideal is not multi-homogenous, please correct this"; return 0;);
    if not isMultiHom(Y) then (print "the second ideal is not multi-homogenous, please correct this"; return 0;);

    R :=ring Y;
    n:=numgens(R)-length unique degrees R;
    IA := intersectionRing(A,n);
    sY := scheme(Y,IA);
    sX := scheme(X+Y,IA);

    --find the max multidegree, write it as a class alpha
    maxDegs := for d in transpose degrees (X+Y) list max d;
    alpha := sum(length IA.codim1Basis,i->(basis(OneAti(degreeLength R,i),A))_0_0*maxDegs_i);
    if opts.Verbose then <<"[Y]= "<<chowClass(sY)<<", alpha= "<<alpha<<endl;

    -- All the hard work is hidden in the next line
    projectiveDegreesList := projectiveDegrees(sX,sY);
    if opts.Verbose then <<"Projective degrees= "<<projectiveDegreesList<<endl;

    --build segre class recursivly from Proj Degs
    segreClass:=0_A;
    RHS:=sum(0..dim sX,i->alpha^(dim sY-i)*chowClass(sY)) - sum(projectiveDegreesList);
    basisByCodim := partition(i -> sum(flatten exponents i), IA.basis);
    for i from 0 to dim sX do (
        for w in basisByCodim#(codim(sX)+i) do (
            L:=(IA.pointClass//w);
            C:=RHS_(w)-(L*(1+alpha)^(dim(sY)-sum(flatten exponents(L)))*segreClass)_(IA.pointClass);
            segreClass=segreClass+C*w;
            --<<"L= "<<L<<", w= "<<w<<", SegClass= "<<segreClass<<" exp (1+alpha)= "<<(dim(sY)-sum(flatten(exponents(L))))<<endl;
        );
    );
    if opts.Verbose then <<"s(X,Y)= "<<segreClass<<endl;
    return segreClass;
);


intersectionProduct=method(TypicalValue => RingElement,Options => {Verbose=>false});
intersectionProduct (Ideal,Ideal,Ideal) :=opts-> (I1,I2,I3) -> (
    A:=makeChowRing(ring(I2));
    return intersectionProduct(I1,I2,I3,A,opts);
);
intersectionProduct (Ideal,Ideal,Ideal,QuotientRing) :=opts->(Ix,Iv,Iy,A) -> (
    --figure out what ambient (product of) projective space/spaces we are in... need to add code for ambient toric
    R:=ring Ix;
    numFactors := degreeLength R;
    factorDims := factorDimensions(R);
    prodSpaceNs:=join(factorDims,factorDims);
    S:= makeProductRing(prodSpaceNs);
    mapFirstFactor:= map(S,R,take(gens S,numgens(R)));
    mapSecondFactor:= map(S,R,drop(gens S,numgens(R)));
    X:= mapFirstFactor(Ix+Iy);
    Y:= mapSecondFactor(Iv+Iy);

    -- split the vars by factor and take 2x2 minors of the sets of matrices
    factorVars := for d in (unique degrees R) list (partition(degree, gens R))#d;
    D := sum (for l in factorVars list minors(2, matrix{mapFirstFactor \ l,mapSecondFactor \ l}));

    seg:=segre(D,X+Y,opts);
    Aprod:=ring seg;
    temp:={};
    termDegrees := degree \ terms seg;
    segrePullbackCoeffs := new HashTable from (
        for t in terms seg list (
            {apply(take(degree t, numFactors), drop(degree t, numFactors), min), (last coefficients t)_(0,0)}
        )
    );
    segrePullbackTerms := for kvpair in pairs segrePullbackCoeffs list (
        (degList,coeff) := kvpair;
        p := product(apply(gens A, degList, (v,d)->v^d));
        --print(p);
        lift(coeff,ZZ) * p
    );
    segrePullback := sum segrePullbackTerms;

    dimY := sum(factorDims) - codim(Iy);
    expectDim:= dimY - codim(Ix,Iy) - codim(Iv,Iy);
    if opts.Verbose then <<"Segre pullback to diagonal = "<<segrePullback<<endl;
    cY:=CSM(A,Iy)//chowClass(Iy,A);
    if opts.Verbose then <<"Chern class = "<< cY <<endl;
    intProduct:=cY*segrePullback;
    return sum select(terms intProduct,j->sum(degree(j))==sum(factorDims)-expectDim);
);

----------------------------
-- utility functions
----------------------------

factorDimensions = R -> (
    -- if R = makeProdRing({a,b,c,...})
    -- then factorDimensions(R) = {a,b,c,...}
    return for deg in unique degrees R list (
        (tally degrees R)#deg - 1
    )
)

codim (Ideal,Ideal) := {} >> opts -> (X,Y) -> (
    -- returns codimension of X in Y
    return codim(X+Y) - codim(Y)
)

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
needsPackage "SegreClasses"
*}
R = makeProductRing({3,3})
x = gens(R)
D = minors(2,matrix{{x_0..x_3},{x_4..x_7}})
X = ideal(x_0*x_1,x_1*x_2,x_0*x_2)
A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^4,b^4)
time s = segre(X,D,A,Verbose=>true)
assert(s == 3*(a^3*b^2+a^2*b^3)-10*(a^3*b^3))
///

TEST ///
{*
restart
needsPackage "SegreClasses"
*}
R=makeProductRing({6})
x=gens(R)
degrees R
I=ideal(random(2,R),x_0^4-x_1*x_3^3-x_4*x_5^3)
J=ideal(x_0*x_2-x_4*x_5)
chowClass(J,Strategy=>"prob")
-- having this here breaks the test (!?).  Separating for now...
-- A = ZZ[h]/(h^7)
-- assert(segre(I,J,A,Verbose=>true)==16*h^3-96*h^4+448*h^5-1920*h^6)
assert(multiplicity(I,J,Verbose=>true)==1)
se=segre(I,J)
pd=projectiveDegrees(I,J)


///

TEST ///
-- union of coordinate axes in PP3 (diagonal)
{*
restart
needsPackage "SegreClasses"
*}
R = makeProductRing({3,3})
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
needsPackage "SegreClasses"
*}
R=makeProductRing({6})
x=gens(R)
degrees R
I=ideal(random(2,R),x_0^4-x_1*x_3^3-x_4*x_5^3)
J=ideal(x_0*x_2-x_4*x_5)
chowClass(J,Strategy=>"prob")
A = ZZ[h]/(h^7)
assert(segre(I,J,A,Verbose=>true)==16*h^3-96*h^4+448*h^5-1920*h^6)
///

TEST ///
{*
restart
needsPackage "SegreClasses"
*}
kk=ZZ/32003
R = kk[x,y,z,w];
X = ideal(-z^2+y*w,-y*z+x*w,-y^2+x*z)
Y = ideal(-z^3+2*y*z*w-x*w^2,-y^2+x*z)
assert(multiplicity(X,Y)==2)
time assert(isComponentContained(X,Y,Verbose=>true)==true)
time assert (isComponentContained(Y,X)==true)


///

TEST ///
{*
restart
needsPackage "SegreClasses"
*}
-- Cx is a hyperplane section on a smooth quadric surface
-- embedded in the diagonal of P3xP3
R=makeProductRing({3,3})
x=(gens(R))_{0..3}
y=(gens(R))_{4..7}
Qx = ideal (x#0*x#1 - x#2*x#3)
Qy=sub(Qx,matrix{join(y,for i from 4 to 7 list 0)})
D = minors(2,matrix{x,y})
I=ideal(Qx,Qy,D) --Q in the diagional
Cx=ideal random({1,0},R)
A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^4,b^4)
s=segre(Cx,I,A,Verbose=>true)
assert(s == 2*(a^3*b^2+a^2*b^3-a^3*b^3))
///

TEST ///
{*
restart
needsPackage "SegreClasses"
*}
R=makeProductRing({2,1});
x=(gens R)_{0..2};
y=(gens R)_{3..4};
I = ideal (x_0,x_1);  -- choosing a simple point to make things easier
B=ideal(y_0*I_1-y_1*I_0); ---blow up of this point...
E=B+ideal (x_0,x_1);
A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^3,b^2)
s=segre(E,B,A,Verbose=>true)
assert(s == a^2 + a^2*b)
///

TEST ///
{*
restart
needsPackage "SegreClasses"
*}
n=6
kk=ZZ/32749
R=kk[x_0..x_n]
A=makeChowRing(R)
X=ideal(x_2*x_3*x_5-5*x_6^2*x_0+3*x_2*x_0*x_1,random(3,R))
Y=ideal mingens(X*X);
time assert(isComponentContained(X,Y,Verbose=>true)==true)
time assert(isComponentContained(Y,X)==true)
Theta=ideal(random(kk)*X_0+random(kk)*X_1)
F=ideal(random(kk)*Y_0+random(kk)*Y_1+random(kk)*Y_2)
time assert(segreDimX(X,Theta,A)==9*A_0^2)
time segreDimX(X,Theta*F,A)
///


TEST ///
{*
restart
needsPackage "SegreClasses"
*}
n=6
kk=ZZ/32749
R=kk[x_0..x_n]
m=matrix{for i from 0 to n-3 list x_i,for i from 0 to n-3 list (i+3)*x_(i+3),for i from 0 to n-3 list x_(i+2),for i from 0 to n-3 list x_(i)+(5+i)*x_(i+1)}
C=ideal mingens(minors(3,m))
P=ideal(x_0,x_4,x_3,x_2,x_1)
time assert(containedInSingularLocus(P,C,Verbose=>true)==true)
///

end


TEST ///
{*
restart
needsPackage "SegreClasses"
*}
kk=ZZ/32729
R = makeProductRing(kk,{2,2,2})
x=(gens R)_{0..2}
y=(gens R)_{3..5}
z=(gens R)_{6..8}
B=ideal(x)*ideal(y)*ideal(z)
m1=matrix{{x_0,x_1,5*x_2},y_{0..2},{2*z_0,7*z_1,25*z_2}}
m2=matrix{{9*z_0,4*z_1,3*z_2},y_{0..2},x_{0..2}}
W=minors(3,m1)+minors(3,m2)
f=random({1,1,1},R)
Y=ideal (z_0*W_0-z_1*W_1)+ideal(f)
X=((W)*ideal(y)+ideal(f))
isSubset(Y,X)
time isSubset(saturate(Y,B),saturate(X,B))
time assert(isComponentContained(X,Y)==true)
///
----------
--other examples in various order
-------

restart
needsPackage "SegreClasses"
kk=ZZ/32749
R = makeProductRing(kk,{2,3})
x=(gens R)_{0..2}
y=(gens R)_{3..6}
I=ideal(x_0^2*x_1*y_1^2-x_0^3*y_0*y_3)
J=ideal(x_1^2*x_0*y_3^2-x_0^3*y_2*y_0-x_0^3*y_0^2)
time seg=segre(I,J)


restart
needsPackage "SegreClasses"
kk=ZZ/32749
R = kk[x,y,z,t]
PP3xPP3 = makeProductRing(kk,{3,3})
m1 = map(PP3xPP3,R,take(gens PP3xPP3,4))
m2 = map(PP3xPP3,R,drop(gens PP3xPP3,4))
f = ideal "x(x2-2xy+zt) + y(x2-3yt+z2+3t2-3tz+xy)"
h = ideal "x(x2-7y2-zt) + y(3x2-5yt)"
g = ideal "x(23xy-34z2-17yt+t2) + y(x2+y2+z2+xy+zt)"
X = m1(f+g)
Y = m2(h+g)
D = minors(2,matrix{take(gens PP3xPP3,4),drop(gens PP3xPP3,4)})
-- this example takes 30secs or so... (07.01.18)
time segre(D,X+Y)

restart
needsPackage "SegreClasses"
R = makeProductRing({3})
I1=ideal random(1,R)
I2=ideal random(1,R)
I3=ideal (R_0^2-34*R_1*R_2+3*R_3^2)
intersectionProduct(I1,I2,I3)

restart
needsPackage "SegreClasses"
R = makeProductRing(QQ,{3})
(x,y,z,w) = toSequence gens R
Q = ideal "xy-zw"
L1 = ideal "x,w"
L2 = ideal "y,w"
intersectionProduct(L1,L2,Q,Verbose=>true)
intersectionProduct(L1,L1,Q,Verbose=>true)

restart
needsPackage "SegreClasses"
R=makeProductRing({2,1});
x=(gens R)_{0..2}
y=(gens R)_{3..4}
I = ideal (x_0,x_1);  -- choosing a simple point to make things easier
B=ideal(y_0*x_1-y_1*x_0); ---blow up of this point...
E=B+ideal (x_0,x_1);
intersectionProduct(E,E,B,Verbose=>true)

restart
needsPackage "SegreClasses"
R = makeProductRing({3,3})
C = makeChowRing(R)
x = gens(R)
D = minors(2,matrix{{x_0..x_3},{x_4..x_7}})
X = ideal(x_0*x_1,x_1*x_2,x_0*x_2)
pds = projectiveDegrees(X,D,Verbose=>true)
l = gens C
p = l#0^3 * l#1^3
projectiveDegree(X,D,p)

restart
needsPackage "SegreClasses"
n=6
kk=ZZ/32749
R=kk[x_0..x_n]
m=matrix{for i from 0 to n-3 list x_i*x_(i+1),for i from 0 to n-3 list x_(i+3)*x_(i+1),for i from 0 to n-3 list x_5*x_(i+2),for i from 0 to n-3 list x_6*x_(i+3)}
C=minors(2,m)
numgens C
decompose C
P=ideal(x_0,x_1,x_3,x_5,x_6)
time multiplicity(P,C)
time containedInSingularLocus(P,C)
time J=minors(4,jacobian(C));
time isSubset(J,P)
restart
needsPackage "SegreClasses"
n=6
kk=ZZ/32749
R=kk[x_0..x_n]
C=ideal(x_0^2+x_1^2,x_3*x_2+x_1*x_3-21*x_4^2,x_3*x_5+x_2*x_3-21*x_5^2)
P=decompose C
isSubset(C,P_0)
isSubset(C,P_1)
time isVarietyContained(P_0,C)
time isVarietyContained(P_1,C)
time multiplicity(P_1,C)

C=ideal(x_0^2+x_1^2,x_3*x_2+x_1*x_3-21*x_4^2,x_3*x_5+x_2*random(1,R)-21*x_5^2)
C=ideal(x_0^2+x_1^2,x_3*x_2^2+55*x_0^2+77*x_0*x_4,x_3*x_5+x_2*random(1,R)-21*x_5^2)
P=decompose C
#P
isSubset(C,P_0)
isSubset(C,P_1)
time isVarietyContained(P_0,C)
time isVarietyContained(P_1,C)

restart
needsPackage "SegreClasses"
R=makeProductRing({6})
x=gens(R)
degrees R
I=ideal(x_0^2*x_1-random(1,R)*x_4^2,x_3*x_4*x_5-23*x_2^3-x_0^2*x_1)
J=ideal(x_0^2*x_2-x_4*x_5^2+x_6^3)
chowClass(J,Strategy=>"prob")

assert(multiplicity(I,J,Verbose=>true)==1)
A=makeChowRing(R)
h=first gens A
se=segre(I,J,A,Verbose=>true)
pd=projectiveDegrees(I,J,A)
alp=3*h
clY=3*h
dY=5
dX=3
le=for i from 0 to dX list clY*alp^(dY-i)//(1-3*h)^(i)
-(last le)+sum(le_{0..2})
s2=sum(0..dX,i->(-1)^(i+1)*(clY*alp^(dY-i)-pd_(dX-i))//(1+3*h)^(i))
se
restart
needsPackage "SegreClasses"
n=5
kk=ZZ/32749
R=kk[x_0..x_n]
Y=ideal(x_0,x_1)
X=ideal(x_1,x_3)
isSubset(X,Y)
time isVarietyContained(Y,X)
time isVarietyContained(X,Y)

isSubset(C,P_0)
isSubset(C,P_1)

time multiplicity(Y,X)
time isVarietyContained(P_1,C)

restart
needsPackage "SegreClasses"
n=6
kk=ZZ/32749
R=kk[x_0..x_n]
m=matrix{for i from 0 to n-3 list x_i,for i from 0 to n-3 list x_(i+3),for i from 0 to n-3 list x_(i+2),for i from 0 to n-3 list x_(i)+x_(i+1)}
C=ideal mingens(minors(3,m)+ideal(x_0*x_1*(x_5)+x_0^3))
P=(decompose C)
for p in P list codim p
(radical C)==C
C=radical C
numgens C
sub(C,{x_0=>0,x_4=>0,x_3=>0,x_2=>0,x_1=>0})
P=ideal(x_0,x_4,x_3,x_2,x_1)
time multiplicity(P,C)
time containedInSingularLocus(P,C)
time J=minors(4,jacobian(C));
time isSubset(J,P)
time isSubset(C,P)
degree C
time codim (J+C)
A=makeChowRing R
time projectiveDegree(P,C,A_0^5)
restart

restart
needsPackage "SegreClasses"
n=6
kk=ZZ/32749
--kk=QQ
R=kk[x_0..x_n]
m=matrix{for i from 0 to n-3 list x_i,for i from 0 to n-3 list (i+3)*x_(i+3),for i from 0 to n-3 list x_(i+2),for i from 0 to n-3 list x_(i)+(5+i)*x_(i+1)}
C=ideal mingens(minors(3,m))
numgens C
codim C
C==radical(C)
#(decompose C)
P=ideal(x_0,x_4,x_3,x_2,x_1)
time containedInSingularLocus(P,C)
time J=minors(4,jacobian(C));
time isSubset(J,P)
time isSubset(C,P)
time J1=radical J;
A=makeChowRing R
time isVarietyContained(P,C)
time projectiveDegree(P,C,A_0^5)
degree C
restart

restart
needsPackage "SegreClasses"
n=4
kk=ZZ/32749
R=kk[x_0..x_n]
Y=ideal random(1,R)
X=ideal(random(2,R),random(2,R))
isVarietyContained(Y*X,Y)
K=X*Y
Z=ideal sum(numgens(K),i->random(kk)*K_i)
segre(K,Z*Z)

codim K
codim Y
codim(X*Y)
m=matrix{for i from 0 to 2 list x_i,for i from 1 to 3 list x_i}
C=ideal mingens(minors(2,m))
I=ideal(x_0^3-x_2*x_3*x_1-5*x_1^2*x_0,12*x_0^2*x_3+13*x_1*x_2^2)
J=ideal(x_1^2-x_2*x_3,12*x_3^2+33*x_0*x_2-x_1^2)
Z=ideal (sum(numgens(I),i->random(kk)*I_i)*sum(numgens(C),i->random(kk)*C_i))
Z=ideal (for i from 0 to 1 list sum(numgens(I),i->random(kk)*I_i))
codim I
degree saturate(Z,I)
degree I
degree Z
degree(C+Z)
codim (C+Z)
projectiveDegrees(C+Z,Z)
projectiveDegrees(C,ideal(sum(numgens(C),i->random(kk)*C_i)))
P=decompose (J*I)
projectiveDegrees(I,J*I)
projectiveDegrees(I,J)
projectiveDegrees(K+J*I,J)
projectiveDegrees(K+J*I,I)
projectiveDegrees(K+J,J)
J==(J+ideal(random(kk)*J_0+random(kk)*J_1)*(ideal(random(kk)*K_0)))
codim(J+ideal(random(kk)*J_0+random(kk)*J_1))
codim(J+K)
degree (K+I)
K=ideal(12*x_0^2+13*x_1*x_2)
codim(I*J+K+I)
time isVarietyContained(K*K,K)
K==radical(K*K)
projectiveDegrees(I,I)

segre(P_0,P_0)
m=matrix{for i from 0 to n-3 list x_i,for i from 0 to n-3 list (i+3)*x_(i+3),for i from 0 to n-3 list x_(i+2),for i from 0 to n-3 list x_(i)+(5+i)*x_(i+1)}
C=ideal mingens(minors(3,m))
codim C
P=ideal(x_0,x_4,x_3,x_2,x_1)
time containedInSingularLocus(P,C)
time J=minors(4,jacobian(C));
time isSubset(J,P)
time isSubset(C,P)
time J1=radical J;
A=makeChowRing R
time isVarietyContained(P,C)
time projectiveDegree(P,C,A_0^5)
degree C
restart

restart
check "SegreClasses"

restart
needsPackage "SegreClasses"
kk=ZZ/32749
R = makeProductRing(kk,{2,3})
x=(gens R)_{0..2}
y=(gens R)_{3..6}
I=ideal(x_0^2*x_1*y_1^2-x_0^3*y_0*y_3)
J=ideal(x_1^2*x_0*y_3^2-x_0^3*y_2*y_0-x_0^3*y_0^2)
time seg=segre(I,J)
restart
needsPackage "SegreClasses"
kk=ZZ/32749
R = kk[x..z]
Y=ideal(x*y)
X=ideal(x^2,x*y,x*z,y*z)
multiplicity(X,Y)
projectiveDegrees(X,Y)
decompose ideal(x_0,x_1,x_0+x_1)
ideal(x_0*x_1,3*x_0)

restart
needsPackage "SegreClasses"
kk=ZZ/32749
R = kk[a..c]
X=ideal "a3,ab,b3"
Y=ideal "a3+(2a+3b+5c)ab-7b3"
Y=ideal "23a3+(2a+344b+55c)ab-7b3"
X=ideal(a^4,a*b^3,b^4)
radical X
G=for i from 0 to 3 list sum((numgens Y),j->random(kk)*Y_j)
F=for i from 0 to 3 list sum((numgens X),j->random(kk)*X_j)
Z=ideal(F_0*G_0)
segre(X,Z,Strategy=>"Sat")
segre(X,Y*ideal(random(2,R)))
chowClass Z
radical(Z+X)
segre(X,ideal(F_0),Strategy=>"Sat")
segre(X,ideal(G_0))
chowClass radical X
Z==radical(Z)
ideal(F_0)==radical(ideal(F_0))
codim X
projectiveDegrees(X,Y)
projectiveDegrees(radical X,Y)
radical X
time isVarietyContained(X,Y)
isSubset((Y),radical(X))
isSubset(Y,X)
radical (ideal(jacobian(Y))+Y)
multiplicity(X,Y)    
degree X
chowClass Y
projectiveDegrees(X,Y)
radical X

NumericalAlgebraicGeometry
X=ideal(a-b,a-2*b,a-2*c,a-c)
Y=ideal random(1,R)
X=ideal(random(2,R),random(2,R))
isVarietyContained(X,Y)

restart
needsPackage "NumericalAlgebraicGeometry"
R=CC[a..c]
X=ideal(a-b,a-2*b,b-c,b-2*c)
w = projectiveWitnessSet(X)
decompose numericalIrreducibleDecomposition X

restart
needsPackage "SegreClasses"
R=makeProductRing({2,3});
x=(gens R)_{0..2}
y=(gens R)_{3..6}
ideal x
I=ideal(x_0*x_1^2*y_1-x_2^3*y_3,x_2*y_2^2-x_1*y_0*y_1)
degrees I
codim I
J=ideal(y)*ideal(I_0)+ideal(for e in x list e^2)*ideal(I_1)
degrees J
I==saturate(J,ideal(x)*ideal(y))
isMultiHom I
tex I


restart
needsPackage "SegreClasses"
kk=ZZ/32749
R = makeProductRing(kk,{3,4})
gens R
x=(gens R)_{0..3}
y=(gens R)_{4..8}
B=ideal(x)*ideal(y)
y2=for c in y list c
m=matrix{for c in x list c^2,y2_{0..3},y2_{1..4}}
f=random({2,2},R)
W=minors(3,m)
decompose W
Y=ideal(y_0*W_0-y_1*W_1)+ideal(x_2*W_2-x_3*W_3)
X=(W)*ideal(x)
degrees X
degrees Y
time isSubset(Y,X)
time isSubset(saturate(Y,B),saturate(X,B))
time isVarietyContained(X,Y)
time isSubset(radical saturate(Y,B),radical saturate(X,B))

decompose Y
restart
needsPackage "SegreClasses"
kk=ZZ/32729
R = makeProductRing(kk,{2,2,2})
gens R
x=(gens R)_{0..2}
y=(gens R)_{3..5}
z=(gens R)_{6..8}
B=ideal(x)*ideal(y)*ideal(z)
m1=matrix{{x_0,x_1,5*x_2},y_{0..2},{2*z_0,7*z_1,25*z_2}}
m2=matrix{{9*z_0,4*z_1,3*z_2},y_{0..2},x_{0..2}}
W=minors(3,m1)+minors(3,m2)
f=random({1,1,1},R)
degrees W
decompose W
degrees W
Y=ideal (z_0*W_0-z_1*W_1)+ideal(f)
degrees Y
X=((W)*ideal(y)+ideal(f))
degrees X
degrees Y
isSubset(Y,X)
time multidegree saturate(X+Y,B)
time isSubset(saturate(Y,B),saturate(X,B))
time isComponentContained(X,Y)


restart
needsPackage "SegreClasses"
kk=ZZ/32749
R = makeProductRing(kk,{2,2,2,1})
gens R
x=(gens R)_{0..2}
y=(gens R)_{3..5}
z=(gens R)_{6..8}
w=(gens R)_{9..10}
B=ideal(x)*ideal(y)*ideal(z)*ideal(w)
m1=matrix{{x_0,x_1,5*x_2},y_{0..2},z_{0..2}}
m2=matrix{{2*x_1,7*x_2,5*x_0},y_{0..2},{3*z_1,7*z_2,15*z_0}}
m3=matrix{{4*x_0^2,3*x_1^2,9*x_0^2},y_{0..2},z_{1..3}}
W=minors(3,m1)+minors(3,m2)
f=random({0,0,0,2},R)
degrees W
saturate(W,B)
decompose W
degrees W
Y=ideal (W_0*w_0-W_1*w_1)*ideal(for c in y list c)*ideal(for c in w list c)+ideal(f)
degrees Y
X=(W)+ideal(f)
degrees X
degrees Y
isSubset(Y,X)
multidegree saturate(X+Y+ideal(f),B)
time isSubset(saturate(Y,B),saturate(X,B))
time isVarietyContained(X,Y)
random({0,0,1},R)


restart
needsPackage "SegreClasses"
n=6
kk=ZZ/32749
--kk=QQ
R=kk[x_0..x_n]
m=matrix{for i from 0 to n-3 list x_i,for i from 0 to n-3 list (i+3)*x_(i+3),for i from 0 to n-3 list x_(i+2),for i from 0 to n-3 list x_(i)+(5+i)*x_(i+1)}
m=matrix{for i from 0 to n-3 list x_i,for i from 0 to n-3 list x_(i+1),for i from 0 to n-3 list x_(i+2),for i from 0 to n-3 list x_(i+3)}--,for i from 0 to n-3 list x_(i)+(5+i)*x_(i+1)}
C=ideal mingens(minors(3,m))
P1=primaryDecomposition C
P2=decompose C
P1==P2
X=ideal(C_0,C_4,C_9)
codim X
P=(primaryDecomposition X)
codim P_0
W=P_0
numgens W
V=ideal (flatten entries gens W)_{0..3}
codim V
numgens V
sub(V,{x_5=>x_5^2})

restart
needsPackage "SegreClasses"
n=6
kk=ZZ/32749
R=kk[x_0..x_n]
X=ideal(x_2*x_3*x_5-5*x_6^2*x_0+3*x_2*x_0*x_1,random(3,R))
Y=ideal mingens(X*X)
time isComponentContained(X,Y)

Theta=ideal(random(kk)*X_0+random(kk)*X_1)
F=ideal(random(kk)*Y_0+random(kk)*Y_1+random(kk)*Y_2)
time segre(X,Theta)
time multiplicity(X,Theta*F)
time segre(Y,F)
time multiplicity(Y,Theta*F)
time radical(X)==radical(Y)




codim X
Y=ideal(x_5*X_0-x_6*X_1,X_2,X_3)
codim ideal(X_0,X_3,X_2)
codim Y
P=primaryDecomposition Y
for p in (decompose Y) list codim p
X==P_1
X==radical(P_0)
codim Y
Y=ideal for i from 0 to 0 list x_(i%6)*X_(2*i)-x_((i+1)%6)*X_(2*i+1)
X
C=X*(ideal gens R)
for i from 0 to 2 list {i%6,(i+1)%6}
time radical(X)==radical(Y)
codim Y
decompose saturate Y
decompose X
numgens C
time isVarietyContained(Y,X)
time isVarietyContained(X,Y)

X=ideal(x_0*x_3

restart
needsPackage "SegreClasses"
kk=ZZ/32003
R = kk[x,y,z,w];
X = ideal(-z^2+y*w,-y*z+x*w,-y^2+x*z)
Y = ideal(-z^3+2*y*z*w-x*w^2,-y^2+x*z)
Y=ideal(z^2*X_0-w^2*X_1,X_2)
radical(Y)
X
assert(multiplicity(X,Y)==2)
radical(X)==radical(Y)
time isSubset(X,Y)
time isSubset(Y,X)



restart
needsPackage "SegreClasses"
n=2
kk=ZZ/32749
R=kk[x_0..x_n]
X=ideal(x_0,x_1)
Y=ideal(x_1^2*x_2-x_0^2*(x_0+x_2))
radical Y
A=makeChowRing R
A_0
projectiveDegree(X,Y,A_0)
ideal mingens (X+Y)
segre(X,Y)


restart
needsPackage "SegreClasses"
n=6
kk=ZZ/32749
R=kk[x_0..x_n]
A=makeChowRing(R)
X=ideal(x_2*x_3*x_5-5*x_6^2*x_0+3*x_2*x_0*x_1,random(3,R))
Y=ideal mingens(X*X);
time isComponentContained(X,Y)
time isComponentContained(Y,X,Verbose=>true)


Theta=ideal(random(kk)*X_0+random(kk)*X_1)
F=ideal(random(kk)*Y_0+random(kk)*Y_1+random(kk)*Y_2)
time segreDimX(X,Theta,A)
time segreDimX(X,Theta*F,A)
time segreDimX(Y,F,A)
time segreDimX(Y,Theta*F,A)


restart
needsPackage "SegreClasses"
R=kk=ZZ/32749
R=kk[w..z]
Y=ideal(0_R)
X=ideal(x,y)*ideal(x^3,x*y,y^3,w)
projectiveDegrees(X,Y)


restart
needsPackage "SegreClasses"
kk = ZZ/32749
R = makeProductRing(kk,{3})
x = gens R
X = intersect(ideal(x_0,x_1), ideal(x_0^3,x_0*x_1,x_1^3,x_2))
Y = ideal (0*R_0)
projectiveDegrees(X,Y)

-- make L very special
L =  ideal (x_0+3*x_1+2*x_2)
Y' = Y + L
X' = X + L
I = makeMultiHom(X',Y')
f2 = sum(numgens I,j->random(kk)*I_j)
f1 = sum(numgens I,j->random(kk)*I_j)
J=saturate(ideal(f1,f2),X)
K=J+minors(2,jacobian(J));
codim saturate K
decompose J
saturate(L+ideal(f1,f2),X)
degree oo

-- now make it general
L = ideal random(1,R)
Y' = Y + L
X' = X + L
I = makeMultiHom(X',Y')
f2 = sum(numgens I,j->random(kk)*I_j)
f1 = sum(numgens I,j->random(kk)*I_j)
saturate(L+ideal(f1,f2),X)
degree oo

restart
needsPackage "SegreClasses"
R = makeProductRing({4})
describe R
x=gens R
l=- 5*x_0 + x_1 - 9*x_2 - 13*x_3 + 12*x_4
m=matrix{{l,x_1,x_2},{x_1,x_2,x_3},{x_2,x_1,x_4}}
K= minors(2,m)
X=ideal(K_1,K_0,K_2)
V=ideal(K_3,K_4,K_5)
codim(V)
Y=ideal(x_3*x_2+23*x_0*x_4-x_1^2)
codim V
codim X
time P=primaryDecomposition(V+Y+X)
degree(V+X)
time for p in P list codim p
time intersectionProduct(X+Y,V+Y,Y,Verbose=>true)
codim saturate (Y+ideal jacobian Y)

X=ideal(l^2-l*x_4,x_4*x_2-l*x_4)
V=ideal(x_4*x_0-l*x_4)
Y=ideal(x_3^2-x_0*x_1+23*x_2*x_4)
degree (X+Y+V)
degree(V+Y)
codim(X+Y)
codim(V+Y)

time for p in P list degree p

time degree(saturate (P_0*P_2))
Z=X+Y+V
J=(Z+minors(codim(Z),jacobian(Z)))
isSubset(J,radical(P_0))
multiplicity (P_2,J,Verbose=>true)
codim J
codim P_1
K=saturate(V+Y+X,P_1)
codim K
degree K
time for p in P list codim p

degree(X+Y)
degree(V+Y)
time degree(saturate (P_0*P_1*P_2*P_3*P_4*P_6*P_7*P_8*P_9))
codim P_5
degree (P_0*P_1*P_2*P_3*P_4*P_6*P_7*P_8*P_9)
degree (X+Y+V)

needsPackage "NumericalAlgebraicGeometry"
S= CC[gens(R)]
Z=sub(X+V+Y,S)
time numericalIrreducibleDecomposition Z
ideal mingens (X+Y)
degree X
codim(V+Y)
print toString ideal mingens (V+Y)
print toString ideal mingens (X+Y)
print toString ideal mingens (Y)
needsPackage "CharacteristicClasses"
Chern Y
codim saturate (Y+ideal jacobian Y)
