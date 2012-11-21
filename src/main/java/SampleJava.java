
public class SampleJava {
    public Integer test(Integer x, Integer y) {
       Integer result = Integer.valueOf(0);
       if (Boolean.valueOf(x.intValue() > y.intValue()).booleanValue()) {
          result = Integer.valueOf(x.intValue() - y.intValue());
       } else {
          result = Integer.valueOf(y.intValue() - x.intValue());
       }
       return result;
    }
}
