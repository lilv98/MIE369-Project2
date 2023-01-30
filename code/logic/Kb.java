package logic;

import java.io.*;
import java.util.*;

public abstract class Kb {

    // Kb status constants
    public static final int INDETERMINATE = 0;
    public static final int TAUTOLOGY     = 1;
    public static final int INCONSISTENT  = 2;

    // Query filename to use (assigns first unused filename)
    public static String QUERY_FILE = null;
    static {QUERY_FILE = "query.in";}
    
    // String interface
    public abstract void       addFOPCFormula(String s);
    public abstract boolean    queryFOPC(String s); // true if kb |- s
    public abstract boolean    queryFOPC(String assume, String query); // true if kb |- s
    
    // Get query information
    public abstract float getQueryTime();
    public abstract int   getNumInfClauses();
    public abstract int   getProofLength();

    // File IO Information
    public abstract void  setQueryFile(String f);

}
