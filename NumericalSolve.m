declare verbose NumericalSolve, 2;

intrinsic NumericalJacobian(
  f::Map[ModTupFld[RngReCom], ModTupFld[RngReCom]]
   :
  eps:=false
  )
  -> Map[ModTupFld[RngReCom], AlgMat[RngReCom]]
  { Given a function f, returns a function that computes a numerical approxiomation Jacobian of f}
  V := Domain(f);
  n := Dimension(V);
  R := BaseRing(V);
  Prec := Precision(R);
  eps := eps cmpeq false select 10^Floor(-Prec/10) else eps;
  df := function(x)
    M := [];
    fx := f(x);
    for i in [1..n] do
      xi := x;
      xi[i] +:= eps;
      fxi := f(xi);
      Append(~M, (fxi-fx)/eps);
    end for;
    return Transpose(Matrix(M));
  end function;

  return map<V -> MatrixAlgebra(R, n) | x :-> df(x)>;
end intrinsic;



intrinsic IsClose(a::ModTupFldElt[RngReCom], b::ModTupFldElt[RngReCom], AbsoluteTolerance::FldReElt, RelativeTolerance::FldReElt) -> BoolElt
 {returns if |a - b| < Max(RelativeTolerance*Max(|a|, |b|), AbsoluteTolerance)}
  return Sqrt(Real(Norm(a - b))) le Maximum(RelativeTolerance * Sqrt(Maximum(Real(Norm(a)), Real(Norm(b)))), AbsoluteTolerance);
end intrinsic;

intrinsic NewtonRaphson(
  f::Map[ModTupFld[RngReCom], ModTupFld[RngReCom]],
  df::Map[ModTupFld[RngReCom], AlgMat[RngReCom]],
  x0::ModTupFldElt[RngReCom],
  AbsoluteTolerance::FldReElt
  :
  fx0:=false,
  MaxIterations:=50,
  RelativeTolerance:=0.0
  ) -> ModTupFld[RngReCom]
{
  Newton-Raphson method to solve f(x) = 0, where f is function between a n-dimensional complex vector space, starting at x = x0.
  fx0 is optional value for f(x0), to potentilly skip one expensive evaluation.
}
  require Domain(f) eq Codomain(f) :
    Sprintf("We expect the domain and codomain of f to identical, instead, we got %o and %o", Domain(f), Codomain(f));
  require Domain(df) eq Domain(f):
    Sprintf("We expect the domain f and its derivative to be identical, instead, we got %o and %o", Domain(f), Domain(df));
  x0 := Domain(f)!x0;
  require Parent(x0) eq Domain(f) : "We expect x0 to be in the domain of f";
  require Dimension(Domain(df))^2 eq Dimension(Codomain(df)): Sprintf("We expect Dimension(Codomain(df)) = %o , to match the square of Dimension(Domain(df)) = %o", Dimension(Codomain(df)), Dimension(Domain(df)));
  require AbsoluteTolerance gt 0: Sprintf("AbsoluteTolerance = %.2o, must be positive", AbsoluteTolerance);
  RelativeTolerance := RealField(BaseRing(Domain(f)))!RelativeTolerance;
  require RelativeTolerance ge 0: Sprintf("RelativeTolerance = %.2o, must be positive", RelativeTolerance);
  n := 0;
  fx0 := fx0 cmpeq false select f(x0) else Vector(fx0);
  dfx0 := df(x0);

  for n in [1..MaxIterations] do
    vprint NumericalSolve: "Newton-Raphson step", n, ": Norm(f(x)) = ", RealField(5)!Norm(fx0);
    y := Vector(dfx0^(-1) * Transpose(Matrix([fx0])));
    x := x0 - y;
    vprint NumericalSolve: "Newton-Raphson step", n, ": Norm(dx) = ", RealField(5)!Sqrt(Norm(y));
    if IsClose(x, x0, AbsoluteTolerance, RelativeTolerance) then
      return x;
    end if;
    x0 := x;
    fx0 := f(x0);
    dfx0 := df(x0);
  end for;
  error Sprintf("Maximum number of iterations %o exceeded", MaxIterations);
  return x0; // never reached
end intrinsic;

intrinsic NewtonRaphson(
  f::Map[ModTupFld[RngReCom], ModTupFld[RngReCom]],
  df::Map[ModTupFld[RngReCom], AlgMat[RngReCom]],
  x0::SeqEnum[RngReComElt],
  AbsoluteTolerance::FldReElt
  :
  fx0:=false,
  MaxIterations:=50,
  RelativeTolerance:=0
  ) -> SeqEnum[RngReComElt]
{ " } //"
  x := NewtonRaphson(f, Vector(x0), df: fx0:=fx0, MaxIterations:=MaxIterations, RelativeTolerance:=RelativeTolerance);
  return Eltseq(x);
end intrinsic;




intrinsic Broyden(
  f::Map[ModTupFld[RngReCom], ModTupFld[RngReCom]],
  x0::ModTupFldElt[RngReCom],
  AbsoluteTolerance::RngReComElt
  :
  fx0:=false,
  dfx0:=false,
  MaxIterations:=50,
  RelativeTolerance:=0
  ) -> ModTupFld[RngReCom]
{
  Applies Broyden method, a generalization of the secand method, to solve f(x) = 0, where f is function between a n-dimensional complex vector space, starting at x = x0.
  It is a quasi-Newton method that, instead of computing the Jacobian at every iteration, it does rank-one updates.
  fx0 is optional value for f(x0), to potentilly skip one expensive evaluation.
  dfx0 is optional value for the Jacobian at x0, otherwise the identity matrix is taken.
}
  n := Dimension(Domain(f));
  R := BaseRing(Domain(f));
  RR := RealField(R);
  prec := Precision(R);
  require Domain(f) eq Codomain(f) :
    Sprintf("We expect the domain and codomain of f to identical, instead, we got %o and %o", Domain(f), Codomain(f));
  x0 := Domain(f)!x0;
  require Parent(x0) eq Domain(f) : "We expect x0 to be in the domain of f";
  require AbsoluteTolerance gt 0: Sprintf("AbsoluteTolerance = %.2o, must be positive", AbsoluteTolerance);
  RelativeTolerance := RR!RelativeTolerance;
  require RelativeTolerance ge 0: Sprintf("RelativeTolerance = %.2o, must be positive", RelativeTolerance);
  fx0 := fx0 cmpeq false select f(x0) else Vector(fx0);
  vprint NumericalSolve: "Broyden step", 0, ": Norm(f(x)) = ", RealField(5)!Norm(fx0);
  // keeps track of an approximate of the inverse of the Jacobian
  H := dfx0 cmpeq false select IdentityMatrix(R, n) else dfx0^-1;
  eps := 10^(-prec/10);
  dx := Vector(R, [eps : _ in [1..n]]);
  dxT := Transpose(Matrix(dx));
  x := x0 + dx;
  fx := f(x);
  dfT := Transpose(Matrix(fx - fx0));

  dH := func<dx, H, dfT | (Transpose(Matrix(dx - Vector(H*dfT))) * Matrix(dx * H))/ (dx * H * dfT)[1]>;
  H +:= dH(dx, H, dfT);

  x0 := x;
  fx0 := fx;

  for n in [1..MaxIterations] do
    vprint NumericalSolve: "Broyden step", n, ": Norm(f(x)) = ", RealField(5)!Norm(fx0);
    dx := -Vector(H * Transpose(Matrix([fx0])));
    vprint NumericalSolve: "Broyden step", n, ": Norm(dx) = ", RealField(5)!Norm(dx);
    x := x0 + dx;
    fx := f(x);
    dfT := Transpose(Matrix(fx - fx0));
    if IsClose(x, x0, AbsoluteTolerance, RelativeTolerance) then
      return x;
    end if;

    H +:= dH(dx, H, dfT);
    vprint NumericalSolve, 2: "Broyden step", n, ": H = ", ChangeRing(H, ComplexField(5));
    x0 := x;
    fx0 := fx;
  end for;
  error Sprintf("Maximum number of iterations %o exceeded", MaxIterations);
  return x0; // never reached
end intrinsic;


intrinsic Broyden(
  f::Map[ModTupFld[RngReCom], ModTupFld[RngReCom]],
  x0::SeqEnum[RngReComElt],
  AbsoluteTolerance::RngReComElt
  :
  fx0:=false,
  dfx0:=false,
  MaxIterations:=50,
  RelativeTolerance:=0
  ) -> ModTupFld[RngReCom]
{ " } // "
x := Broyden(f, Vector(x0) : fx0:=fx0, dfx0:=dfx0, MaxIterations:=MaxIterations, RelativeTolerance:=RelativeTolerance);
  return Eltseq(x);
end intrinsic;







