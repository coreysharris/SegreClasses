# SegreClasses

The main method provided by this Macaulay2 package is `segre`.  In its most basic form, it accepts a pair of ideals (I, J) in a multigraded ring with I containing J.  Then `segre(I,J)` returns a class in the Chow group of the ambient space.  Currently the ambient space should be a product of finitely many projective spaces.  A future version of this package will allow for computations in more general toric varieties.

## First example

Let's compute the Segre class of the exceptional divisor for the blowup of a point in the plane.

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
