package MiniC.Scanner;

public class SourceFile {

  java.io.File source_file;
  java.io.FileInputStream source;
  final char EOL = '\n';
  public final static char EOF = '\u0000';

  public SourceFile (String filename) {
    try {
       source_file = new java.io.File(filename);
       source = new java.io.FileInputStream(source_file);
    } catch (java.io.IOException e) {
       System.err.println("Error opening file " + filename);
       System.err.println("Exiting...");
       System.exit(1);
    }
  }

  public char readChar()
  {
     try {
        int c = source.read();
        if (c == -1) {
           c = EOF;
        }
        return (char) c;
     } catch (java.io.IOException e) {
        return EOF;
     }
  }

}
