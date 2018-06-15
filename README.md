# SegreClasses

This Macaulay2 package provides six main methods: 'segre', 'multiplicty' ,`projectiveDegrees', `containedInSingularLocus', `isComponentContained' and, 'intersectionProduct' .  Currently the ambient space should be a product of finitely many projective spaces.  A future version of this package will allow for computations in more general toric varieties.

## Computing a Segre class:

Let's compute the Segre class of the exceptional divisor for the blowup of a point in the plane. In its most basic form, the segre method accepts a pair of ideals (I, J) in a multigraded ring with I containing J.  Then `segre(I,J)` returns a class in the Chow group of the ambient space.  

We begin by loading the package:

    needsPackage "SegreClasses"
    
The method `makeProductRing` accepts a list of integers and makes the corresponding product of projective spaces.  In our exapmles, we'll make the homogeneous coordinate ring for PP^2 x PP^1.  In this example we rename the variables.

    R = makeProductRing({2,1});
    x = (gens R)_{0..2}; -- x_0, x_1, x_2
    y = (gens R)_{3..4}; -- y_0, y_1

    I = ideal (x_0,x_1);         -- origin in PP^2
    B = ideal (y_0*x_1-y_1*x_0); -- blow up of this point
    E = B + ideal (x_0,x_1);     -- the exceptional divisor
    
    segre(E,B)

This returns 

          2      2
    o8 = h h  + h
          1 2    1

If we prefer, we can specify our own Chow ring:

    A = ZZ[a,b,Degrees=>{{1,0},{0,1}}]/(a^3,b^2)
    segre(E,B,A)
    
           2     2
    o10 = a b + a
    
## Algebraic Multiplicty 

Below is an example where we compute the algebraic multiplicity of a variety inside an irreducible scheme

    restart
    needsPackage "SegreClasses"
    kk=ZZ/32749
    R = kk[x,y,z,w];
    
Consider the twisted cubic X in PP^3 and a subscheme Y of PP^3 containing the twisted cubic   
    
    X = ideal(-z^2+y*w,-y*z+x*w,-y^2+x*z)    
    Y = ideal(-z^3+2*y*z*w-x*w^2,-y^2+x*z)
    
We see that in fact Y is a `doubly' twisted cubic by computing that X has algebraic multiplcity 2 on Y, i.e. e_XY=2:   
    
    multiplicity(X,Y)
    o7 = 2
    
## Containment of the irreducible components of one scheme in another:

Below is an example where we verify that one variety contains another in a product of projective spaces PP^2 x PP^2 x PP^2:

    R = makeProductRing({2,2,2})
    x=(gens R)_{0..2}
    y=(gens R)_{3..5}
    z=(gens R)_{6..8}
    
The irrelevant ideal of the ambient space is:  

    B=ideal(x)*ideal(y)*ideal(z)

We now define two multi-graded ideals X, Y    

    m1=matrix{{x_0,x_1,5*x_2},y_{0..2},{2*z_0,7*z_1,25*z_2}};
    m2=matrix{{9*z_0,4*z_1,3*z_2},y_{0..2},x_{0..2}};
    W=minors(3,m1)+minors(3,m2);
    f=random({1,1,1},R);
    Y=ideal (z_0*W_0-z_1*W_1)+ideal(f)
    X=((W)*ideal(y)+ideal(f))
    
Now we check that the variety X is contained in the variety Y:

    time isComponentContained(X,Y)
         -- used 2.31366 seconds
    o12 = true

To use classical methods we would have to saturate out the irrevant ideals and then test ideal containment as follows:   

    time isSubset(saturate(Y,B),saturate(X,B))
         -- used 11.2451 seconds
    o14 = true

## Containment in the Singular Locus of a Variety:

There is also a method to test containment of a vareity in the singular locus of another, without computing the defining equations of the singular locus:

    n=6
    R = makeProductRing({n})
    x=gens(R)
    m=matrix{for i from 0 to n-3 list x_i,for i from 0 to n-3 list (i+3)*x_(i+3),for i from 0 to n-3 list x_(i+2),for i from 0 to n-3 list x_(i)+(5+i)*x_(i+1)}
    C=ideal mingens(minors(3,m));
    P=ideal(x_0,x_4,x_3,x_2,x_1)
    
We now confirm that V(P) is contained in the singular locus of V(C)    
    
    containedInSingularLocus(P,C)
    o8 = true

## Intersection products

The package can also compute intersection products, in a sense.  Given subvarieties X,V of a smooth variety Y in some ambient variety M (a product of projective spaces), we can compute the push-forward to M of the intersection product of V on X in Y.

As a very basic example, consider the smooth quadric Q in PP^3, together with lines L1, L2 from the two rulings.

    R = makeProductRing(QQ,{3})
    (x,y,z,w) = toSequence gens R
    Q = ideal "xy-zw"
    L1 = ideal "x,w"
    L2 = ideal "y,w"
    
We can compute the intersection product L1.L2 in Q.
    
    intersectionProduct(L1,L2,Q,Verbose=>true)
       
           3
    o16 = h
           1

We can also compute the self-intersection of one of the lines.

    intersectionProduct(L1,L1,Q,Verbose=>true)
    
    o17 = 0
