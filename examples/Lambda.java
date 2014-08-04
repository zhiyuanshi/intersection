// \(x : Int). x

abstract class Closure
{
  Object x;
  Object out;
  abstract void apply ();
}

public class Lambda
{
  static Object apply ()
  {
    class Fun1 extends Closure
    {
      void apply () { out = x; }
    }
    return new Fun1();
  }
  public static void main (String[] args)
  {
    System.out.println(apply());
  }
}
