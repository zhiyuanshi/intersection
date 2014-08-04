// expression: (\(x : (Int & (Int -> Int))). x) (\(x : Int). x ,, 1) 1
// value:  1

abstract class Closure
{
  Object x;
  Object out;
  abstract void apply ();
}

public class App
{
  static Object apply ()
  {
    class Fun1 extends Closure
    {
      void apply () { out = x; }
    }
    Closure fun1 = new Fun1();
    fun1.x = 1;
    fun1.apply();
    return fun1.out;
  }
  public static void main (String[] args)
  {
    System.out.println(apply());
  }
}
