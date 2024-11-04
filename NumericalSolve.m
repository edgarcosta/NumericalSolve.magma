function NumericalJacobian(f)
  // Given a function f, produce a function that numerically computes the Jacobian of f.
  // Precision is lost by a factor 1/2, which should not matter so much for Newton-Raphson.
  df := function(x : fx:=false)
    prec := Precision(BaseRing(x));
    d := 10^Floor(-prec/2);
    n := NumberOfRows(x);
    M := [];
    if fx cmpeq false then
      fx := f(x);
    end if;
    for i in [1..n] do
      xi := x;
      xi[i] +:= d;
      fxi := f(xi);
      Append(~M, (fxi-fx)/d);
    end for;
      return Transpose(Matrix(M));
  end function;
  return df;
end function;


declare verbose NewtonRaphson, 1;

// This implements Newton-Raphson for a function C^n -> C^n.
// This even works when the derivative is not available; numerical differentiation will be used.
function NewtonRaphsonFn(f, x0 : Derivative:=false, fx0:=false, prec:=false)
  assert Domain(f) eq Codomain(f);// "We expect the domain and codomain of f to identical";
  assert Parent(x0) eq Domain(f); // "We expect x0 to be in the domain of f";
  n := 0;
  if prec cmpeq false then
    prec := Precision(BaseRing(x0));
  end if;
  xn := x0;
  dif := 1.0;
  if Derivative cmpeq false then
    df := NumericalJacobian(f);
  else
    df := Derivative;
  end if;
  while dif gt RealField(prec)!10^(2-prec) and n lt 100 do
    n +:= 1;
    xprev := xn;
    if n eq 1 and fx0 cmpne false then
      fxn := Vector(fx0);
    else
      fxn := f(xn);
    end if;
    dxn := df(xn : fx:=fxn);
    assert Abs(Determinant(dxn)) gt 10^-Floor(prec/10);
    xn -:= Vector(dxn^(-1)*Transpose(Matrix([fxn])));
    dif := Abs(Determinant(dxn))*&+[ Real(Norm(xn[i] - xprev[i])) / Max(1, Abs(xn[i])) : i in [1..NumberOfRows(xn)]]^(0.5);
    if n gt 5 then
      assert(dif lt 1);
    end if;
    vprint NewtonRaphson: "Newton-Raphson step", n, ": ", dif;
  end while;
  return xn;
end function;


/*

SetDefaultRealFieldPrecision(100);
V := VectorSpace(ComplexField(), 1);
f := map<V->V|x:->Vector([x[1]^2 + x[1] - 1])>;
NewtonRaphson(f, Vector([ComplexField() | -1.618]));

V := VectorSpace(RealField(), 1);
f := map<V->V|x:->Vector([x[1]^2 + x[1] - 1])>;
NewtonRaphson(f, Vector([-1.618]));
(-1.618033988749894848204586834365638117720309179805762862135448622705260462818902449707207204189391137)
*/

intrinsic NewtonRaphson(f::Map[ModTupFld[FldCom], ModTupFld[FldCom]], x0::ModTupFldElt[FldCom] : Derivative:=false, fx0:=false, prec:=false) -> ModTupFld[FldCom]
{
  Newton-Raphson method to solve f(x) = 0, where f is function between a n-dimensional complex vector space, starting at x = x0.
  The Derivative may be given as a map df : C^n -> C^(n * n), otherwise, numerical differentiation will be used via forward Euler method.
  fx0 is optional value for f(x0).
  prec is the desired accuracy.
}
  require Domain(f) eq Codomain(f) : "We expect the domain and codomain of f to identical";
  x0 := Domain(f)!x0;
  require Parent(x0) eq Domain(f) : "We expect x0 to be in the domain of f";
  return NewtonRaphsonFn(f, x0 : Derivative:=Derivative, fx0:=fx0, prec:=prec);
end intrinsic;

intrinsic NewtonRaphson(f::Map[ModTupFld[FldRe], ModTupFld[FldRe]], x0::ModTupFldElt[FldRe] : Derivative:=false, fx0:=false, prec:=false) -> ModTupFld[FldRe]
{ " } //"
  require Domain(f) eq Codomain(f) : "We expect the domain and codomain of f to identical";
  x0 := Domain(f)!x0;
  require Parent(x0) eq Domain(f) : "We expect x0 to be in the domain of f";
  return NewtonRaphsonFn(f, x0 : Derivative:=Derivative, fx0:=fx0, prec:=prec);
end intrinsic;


intrinsic NewtonRaphson(f::Map[ModTupFld[FldCom], ModTupFld[FldCom]], x0::SeqEnum[FldComElt] : Derivative:=false, fx0:=false, prec:=false) -> SeqEnum[FldComElt]
{ " } //"
  x := NewtonRaphson(f, Vector(x0) : Derivative:=Derivative, fx0:=fx0, prec:=prec);
  return Eltseq(x);
end intrinsic;


intrinsic NewtonRaphson(f::Map[ModTupFld[FldCom], ModTupFld[FldCom]], x0::ModMatFldElt[FldCom] : Derivative:=false, fx0:=false, prec:=false) -> ModMatFldElt[FldCom]
{ " } //"
  x := NewtonRaphson(f, Vector(x0) : Derivative:=Derivative, fx0:=fx0, prec:=prec);
  return Matrix([x]);
end intrinsic;


intrinsic NewtonRaphson(f::Map[ModTupFld[FldRe], ModTupFld[FldRe]], x0::SeqEnum[FldReElt] : Derivative:=false, fx0:=false, prec:=false) -> SeqEnum[FldReElt]
{ " } //"
  x := NewtonRaphson(f, Vector(x0) : Derivative:=Derivative, fx0:=fx0, prec:=prec);
  return Eltseq(x);
end intrinsic;


intrinsic NewtonRaphson(f::Map[ModTupFld[FldRe], ModTupFld[FldRe]], x0::ModMatFldElt[FldRe] : Derivative:=false, fx0:=false, prec:=false) -> ModMatFldElt[FldRe]
{ " } //"
  x := NewtonRaphson(f, Vector(x0) : Derivative:=Derivative, fx0:=fx0, prec:=prec);
  return Matrix([x]);
end intrinsic;



