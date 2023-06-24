/*  
* Dillon Latimore
* DES.java
* My implementation of the DES encryption/decryption created for a university assignment
* in Data Security. Performs encryption/decryption. Also analyses the DES algorithm in various
* configurations.
*/

import java.io.File;
import java.io.FileNotFoundException;
import java.net.URL;
import java.util.Scanner;
import java.util.concurrent.CountDownLatch;
import java.nio.charset.StandardCharsets;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.FileWriter;
import java.io.BufferedWriter;
import java.io.PrintWriter;


public class DES {
    // keys
    private static boolean[][][] keys = new boolean[2][16][48];

    // initial key permutation
	private static int[] PC1 = { 57, 49, 41, 33, 25, 17, 9, 1, 58, 50, 42, 34,
        26, 18, 10, 2, 59, 51, 43, 35, 27, 19, 11, 3, 60, 52, 44, 36, 63,
        55, 47, 39, 31, 23, 15, 7, 62, 54, 46, 38, 30, 22, 14, 6, 61, 53,
        45, 37, 29, 21, 13, 5, 28, 20, 12, 4 };

    // key permutation at each round
	private static int[] PC2 = { 14, 17, 11, 24, 1, 5, 3, 28, 15, 6, 21, 10,
        23, 19, 12, 4, 26, 8, 16, 7, 27, 20, 13, 2, 41, 52, 31, 37, 47, 55,
        30, 40, 51, 45, 33, 48, 44, 49, 39, 56, 34, 53, 46, 42, 50, 36, 29,
        32 };

    // initial permuation table
    private static int[] IP = { 58, 50, 42, 34, 26, 18, 10, 2, 60, 52, 44, 36,
            28, 20, 12, 4, 62, 54, 46, 38, 30, 22, 14, 6, 64, 56, 48, 40, 32,
            24, 16, 8, 57, 49, 41, 33, 25, 17, 9, 1, 59, 51, 43, 35, 27, 19,
            11, 3, 61, 53, 45, 37, 29, 21, 13, 5, 63, 55, 47, 39, 31, 23, 15, 7 };

    // inverse initial permutation
	private static int[] invIP = { 40, 8, 48, 16, 56, 24, 64, 32, 39, 7, 47,
        15, 55, 23, 63, 31, 38, 6, 46, 14, 54, 22, 62, 30, 37, 5, 45, 13,
        53, 21, 61, 29, 36, 4, 44, 12, 52, 20, 60, 28, 35, 3, 43, 11, 51,
        19, 59, 27, 34, 2, 42, 10, 50, 18, 58, 26, 33, 1, 41, 9, 49, 17,
        57, 25 };

    // permutation P in feistel function
    private static int[] P = { 16, 7, 20, 21, 29, 12, 28, 17, 1, 15, 23, 26, 5,
        18, 31, 10, 2, 8, 24, 14, 32, 27, 3, 9, 19, 13, 30, 6, 22, 11, 4,
        25};

    // expansion table from function f
	private static int[] expandTbl = { 32, 1, 2, 3, 4, 5, 4, 5, 6, 7, 8, 9, 8,
        9, 10, 11, 12, 13, 12, 13, 14, 15, 16, 17, 16, 17, 18, 19, 20, 21,
        20, 21, 22, 23, 24, 25, 24, 25, 26, 27, 28, 29, 28, 29, 30, 31, 32,
        1 };

    // inverse expansion table for des2
    private static int[] invExpand = {0, 5, 6, 11, 12, 17, 18, 23, 24, 29, 30, 35, 36, 41, 42, 47};
    
    // s boxes
    private static int[][][] sboxes = {
        { 		{ 14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7 },
                { 0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8 },
                { 4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0 },
                { 15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13 } 
        },
        { 		{ 15, 1, 8, 14, 6, 11, 3, 2, 9, 7, 2, 13, 12, 0, 5, 10 },
                { 3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5 },
                { 0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15 },
                { 13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9 } 
        },
        { 		{ 10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8 },
                { 13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1 },
                { 13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7 },
                { 1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12 } 
        },
        { 		{ 7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15 },
                { 13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9 },
                { 10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4 },
                { 3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14 } 
        },
        { 		{ 2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9 },
                { 14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6 },
                { 4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14 },
                { 11, 8, 12, 7, 1, 14, 2, 12, 6, 15, 0, 9, 10, 4, 5, 3 } 
        },
        { 		{ 12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11 },
                { 10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8 },
                { 9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6 },
                { 4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13 }

        },
        { 		{ 4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1 },
                { 13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6 },
                { 1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2 },
                { 6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12 }

        },
        { 		{ 13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7 },
                { 1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2 },
                { 7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8 },
                { 2, 1, 14, 7, 4, 10, 18, 13, 15, 12, 9, 0, 3, 5, 6, 11 }

        } };
    
    // left shift for each round
	private static int[] leftShiftArray = { 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1 };

    // dimension 1 - test number
    // dimension 2 - DES version
    // dimension 3 - round
    // dimension 4 - boolean array

    // holds encryption results
    private static boolean results[][][][] = new boolean[4][4][16][64];
    
    //encrypted boolean array
    private static boolean[] e = new boolean[64];
    
    // key 1
    private static boolean[] daKey = new boolean[64];

    public static void main(String[] args) {

        // create output file
        File file = new File("output.txt");
        if (file.exists()) {
            if (file.delete()) {
                System.out.println("File deleted successfully.");
            } else {
                System.out.println("Unable to delete the file.");
            }
        } else {
            System.out.println("File does not exist in the current working directory.");
        }
        
        try(FileWriter fw = new FileWriter(file, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw))
        {
        
        // create a boolean array from plaintext 1
        boolean[] textArray1 = readFile(0);
        
        // create a boolean array from plaintext 2
        boolean[] textArray2 = readFile(1);
        
        // create a boolean array from key 1
        boolean[] keyArray1 = readFile(2);
        
        // create a boolean array from key 2
        boolean[] keyArray2 = readFile(3);
        
        // generate keys
        keyGen(keyArray1, 0);
        keyGen(keyArray2, 1);

        // avalanche demos

        // P under K
        long startTime = System.currentTimeMillis();
        boolean[] e00 = encrypt(textArray1, false, 0, 0, 0);
        long endTime = System.currentTimeMillis();
        long timeElapsed = endTime -startTime;
        boolean[] e01 = encrypt(textArray1, false, 1, 0, 0);
        boolean[] e02 = encrypt(textArray1, false, 2, 0, 0);
        boolean[] e03 = encrypt(textArray1, false, 3, 0, 0);
        
        // P' under K
        boolean[] e10 = encrypt(textArray2, false, 0, 1, 0);
        boolean[] e11 = encrypt(textArray2, false, 1, 1, 0);
        boolean[] e12 = encrypt(textArray2, false, 2, 1, 0);
        boolean[] e13 = encrypt(textArray2, false, 3, 1, 0);

        // P under K
        boolean[] e20 = encrypt(textArray1, false, 0, 2, 0);
        boolean[] e21 = encrypt(textArray1, false, 1, 2, 0);
        boolean[] e22 = encrypt(textArray1, false, 2, 2, 0);
        boolean[] e23 = encrypt(textArray1, false, 3, 2, 0);

        // P under K'
        boolean[] e30 = encrypt(textArray1, false, 0, 3, 1);
        boolean[] e31 = encrypt(textArray1, false, 1, 3, 1);
        boolean[] e32 = encrypt(textArray1, false, 2, 3, 1);
        boolean[] e33 = encrypt(textArray1, false, 3, 3, 1);
        
        // create output
        out.println("Avalanche Demonstration");
        out.println("Plaintext P:  " + returnBoolArray(textArray1));
        out.println("Plaintext P': " + returnBoolArray(textArray2));
        out.println("Key K:  " + returnBoolArray(keyArray1));
        out.println("Key K': " + returnBoolArray(keyArray2));
        out.println("Total running time: " + timeElapsed/1000 + " (second)");
        out.println("");
        out.println("P and P' under K");
        out.println("Ciphertext C:  " + returnBoolArray(e00));
        out.println("Ciphertext C': " + returnBoolArray(e10));
        out.println("Round      DES0      DES1      DES2      DES3");
        out.println("   0        1         1         1         1");
        out.println("   1        " + compareDiff(results[0][0][0], results[1][0][0]) + "         "
                                   + compareDiff(results[0][1][0], results[1][1][0]) + "         " 
                                   + compareDiff(results[0][2][0], results[1][2][0]) + "         "
                                   + compareDiff(results[0][3][0], results[1][3][0]) );
        
        out.println("   2        " + compareDiff(results[0][0][1], results[1][0][1]) + "         "
        + compareDiff(results[0][1][1], results[1][1][1]) + "         " 
        + compareDiff(results[0][2][1], results[1][2][1]) + "         "
        + compareDiff(results[0][3][1], results[1][3][1]) );
        out.println("   3        " + compareDiff(results[0][0][2], results[1][0][2]) + "         "
        + compareDiff(results[0][1][2], results[1][1][2]) + "         " 
        + compareDiff(results[0][2][2], results[1][2][2]) + "         "
        + compareDiff(results[0][3][2], results[1][3][2]) );
        out.println("   4        " + compareDiff(results[0][0][3], results[1][0][3]) + "         "
        + compareDiff(results[0][1][3], results[1][1][3]) + "         " 
        + compareDiff(results[0][2][3], results[1][2][3]) + "         "
        + compareDiff(results[0][3][3], results[1][3][3]) );
        out.println("   5        " + compareDiff(results[0][0][4], results[1][0][4]) + "         "
        + compareDiff(results[0][1][4], results[1][1][4]) + "         " 
        + compareDiff(results[0][2][4], results[1][2][4]) + "         "
        + compareDiff(results[0][3][4], results[1][3][4]) );
        out.println("   6        " + compareDiff(results[0][0][5], results[1][0][5]) + "         "
        + compareDiff(results[0][1][5], results[1][1][5]) + "         " 
        + compareDiff(results[0][2][5], results[1][2][5]) + "         "
        + compareDiff(results[0][3][5], results[1][3][5]) );
        out.println("   7        " + compareDiff(results[0][0][6], results[1][0][6]) + "         "
        + compareDiff(results[0][1][6], results[1][1][6]) + "         " 
        + compareDiff(results[0][2][6], results[1][2][6]) + "         "
        + compareDiff(results[0][3][6], results[1][3][6]) );
        out.println("   8        " + compareDiff(results[0][0][7], results[1][0][7]) + "         "
        + compareDiff(results[0][1][7], results[1][1][7]) + "         " 
        + compareDiff(results[0][2][7], results[1][2][7]) + "         "
        + compareDiff(results[0][3][7], results[1][3][7]) );
        out.println("   9        " + compareDiff(results[0][0][8], results[1][0][8]) + "         "
        + compareDiff(results[0][1][8], results[1][1][8]) + "         " 
        + compareDiff(results[0][2][8], results[1][2][8]) + "         "
        + compareDiff(results[0][3][8], results[1][3][8]) );
        out.println("   10        " + compareDiff(results[0][0][9], results[1][0][9]) + "         "
        + compareDiff(results[0][1][9], results[1][1][9]) + "         " 
        + compareDiff(results[0][2][9], results[1][2][9]) + "         "
        + compareDiff(results[0][3][9], results[1][3][9]) );
        out.println("   11        " + compareDiff(results[0][0][10], results[1][0][10]) + "         "
        + compareDiff(results[0][1][10], results[1][1][10]) + "         " 
        + compareDiff(results[0][2][10], results[1][2][10]) + "         "
        + compareDiff(results[0][3][10], results[1][3][10]) );
        out.println("   12        " + compareDiff(results[0][0][11], results[1][0][11]) + "         "
        + compareDiff(results[0][1][11], results[1][1][11]) + "         " 
        + compareDiff(results[0][2][11], results[1][2][11]) + "         "
        + compareDiff(results[0][3][11], results[1][3][11]) );
        out.println("   13        " + compareDiff(results[0][0][12], results[1][0][12]) + "         "
        + compareDiff(results[0][1][12], results[1][1][12]) + "         " 
        + compareDiff(results[0][2][12], results[1][2][12]) + "         "
        + compareDiff(results[0][3][12], results[1][3][12]) );
        out.println("   14        " + compareDiff(results[0][0][13], results[1][0][13]) + "         "
        + compareDiff(results[0][1][13], results[1][1][13]) + "         " 
        + compareDiff(results[0][2][13], results[1][2][13]) + "         "
        + compareDiff(results[0][3][13], results[1][3][13]) );
        out.println("   15        " + compareDiff(results[0][0][14], results[1][0][14]) + "         "
        + compareDiff(results[0][1][14], results[1][1][14]) + "         " 
        + compareDiff(results[0][2][14], results[1][2][14]) + "         "
        + compareDiff(results[0][3][14], results[1][3][14]) );
        out.println("   16        " + compareDiff(results[0][0][15], results[1][0][15]) + "         "
        + compareDiff(results[0][1][15], results[1][1][15]) + "         " 
        + compareDiff(results[0][2][15], results[1][2][15]) + "         "
        + compareDiff(results[0][3][15], results[1][3][15]) );

        out.println("P under K and K'");
        out.println("Ciphertext C:  " + returnBoolArray(e00));
        out.println("Ciphertext C': " + returnBoolArray(e30));
        out.println("Round      DES0      DES1      DES2      DES3");
        out.println("   0        1         1         1         1");
        

        out.println("   1        " + compareDiff(results[2][0][0], results[3][0][0]) + "         "
                                   + compareDiff(results[2][1][0], results[3][1][0]) + "         " 
                                   + compareDiff(results[2][2][0], results[3][2][0]) + "         "
                                   + compareDiff(results[2][3][0], results[3][3][0]) );
        
        out.println("   2        " + compareDiff(results[2][0][1], results[3][0][1]) + "         "
        + compareDiff(results[2][1][1], results[3][1][1]) + "         " 
        + compareDiff(results[2][2][1], results[3][2][1]) + "         "
        + compareDiff(results[2][3][1], results[3][3][1]) );
        out.println("   3        " + compareDiff(results[2][0][2], results[3][0][2]) + "         "
        + compareDiff(results[2][1][2], results[3][1][2]) + "         " 
        + compareDiff(results[2][2][2], results[3][2][2]) + "         "
        + compareDiff(results[2][3][2], results[3][3][2]) );
        out.println("   4        " + compareDiff(results[2][0][3], results[3][0][3]) + "         "
        + compareDiff(results[2][1][3], results[3][1][3]) + "         " 
        + compareDiff(results[2][2][3], results[3][2][3]) + "         "
        + compareDiff(results[2][3][3], results[3][3][3]) );
        out.println("   5        " + compareDiff(results[2][0][4], results[3][0][4]) + "         "
        + compareDiff(results[2][1][4], results[3][1][4]) + "         " 
        + compareDiff(results[2][2][4], results[3][2][4]) + "         "
        + compareDiff(results[2][3][4], results[3][3][4]) );
        out.println("   6        " + compareDiff(results[2][0][5], results[3][0][5]) + "         "
        + compareDiff(results[2][1][5], results[3][1][5]) + "         " 
        + compareDiff(results[2][2][5], results[3][2][5]) + "         "
        + compareDiff(results[2][3][5], results[3][3][5]) );
        out.println("   7        " + compareDiff(results[2][0][6], results[3][0][6]) + "         "
        + compareDiff(results[2][1][6], results[3][1][6]) + "         " 
        + compareDiff(results[2][2][6], results[3][2][6]) + "         "
        + compareDiff(results[2][3][6], results[3][3][6]) );
        out.println("   8        " + compareDiff(results[2][0][7], results[3][0][7]) + "         "
        + compareDiff(results[2][1][7], results[3][1][7]) + "         " 
        + compareDiff(results[2][2][7], results[3][2][7]) + "         "
        + compareDiff(results[2][3][7], results[3][3][7]) );
        out.println("   9        " + compareDiff(results[2][0][8], results[3][0][8]) + "         "
        + compareDiff(results[2][1][8], results[3][1][8]) + "         " 
        + compareDiff(results[2][2][8], results[3][2][8]) + "         "
        + compareDiff(results[2][3][8], results[3][3][8]) );
        out.println("   10        " + compareDiff(results[2][0][9], results[3][0][9]) + "         "
        + compareDiff(results[2][1][9], results[3][1][9]) + "         " 
        + compareDiff(results[2][2][9], results[3][2][9]) + "         "
        + compareDiff(results[2][3][9], results[3][3][9]) );
        out.println("   11        " + compareDiff(results[2][0][10], results[3][0][10]) + "         "
        + compareDiff(results[2][1][10], results[3][1][10]) + "         " 
        + compareDiff(results[2][2][10], results[3][2][10]) + "         "
        + compareDiff(results[2][3][10], results[3][3][10]) );
        out.println("   12        " + compareDiff(results[2][0][11], results[3][0][11]) + "         "
        + compareDiff(results[2][1][11], results[3][1][11]) + "         " 
        + compareDiff(results[2][2][11], results[3][2][11]) + "         "
        + compareDiff(results[2][3][11], results[3][3][11]) );
        out.println("   13        " + compareDiff(results[2][0][12], results[3][0][12]) + "         "
        + compareDiff(results[2][1][12], results[3][1][12]) + "         " 
        + compareDiff(results[2][2][12], results[3][2][12]) + "         "
        + compareDiff(results[2][3][12], results[3][3][12]) );
        out.println("   14        " + compareDiff(results[2][0][13], results[3][0][13]) + "         "
        + compareDiff(results[2][1][13], results[3][1][13]) + "         " 
        + compareDiff(results[2][2][13], results[3][2][13]) + "         "
        + compareDiff(results[2][3][13], results[3][3][13]) );
        out.println("   15        " + compareDiff(results[2][0][14], results[3][0][14]) + "         "
        + compareDiff(results[2][1][14], results[3][1][14]) + "         " 
        + compareDiff(results[2][2][14], results[3][2][14]) + "         "
        + compareDiff(results[2][3][14], results[3][3][14]) );
        out.println("   16        " + compareDiff(results[2][0][15], results[3][0][15]) + "         "
        + compareDiff(results[2][1][15], results[3][1][15]) + "         " 
        + compareDiff(results[2][2][15], results[3][2][15]) + "         "
        + compareDiff(results[2][3][15], results[3][3][15]) );
        
        e = e00;
        daKey = keyArray1;
        
        } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }

        // create decryption input file
        File file2 = new File("decryptionInput.txt");
        if (file2.exists()) {
            if (file2.delete()) {
                System.out.println("File deleted successfully.");
            } else {
                System.out.println("Unable to delete the file.");
            }
        } else {
            System.out.println("File does not exist in the current working directory.");
        }

        try(FileWriter fw = new FileWriter(file2, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw))
        {
            out.println(returnBoolArray(e));
            out.println(returnBoolArray(daKey));
            
        } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }

        // create decryption output file
        File file3 = new File("decryptionOut.txt");
        if (file3.exists()) {
            if (file3.delete()) {
                System.out.println("File deleted successfully.");
            } else {
                System.out.println("Unable to delete the file.");
            }
        } else {
            System.out.println("File does not exist in the current working directory.");
        }

        try(FileWriter fw = new FileWriter(file3, true);
            BufferedWriter bw = new BufferedWriter(fw);
            PrintWriter out = new PrintWriter(bw))
        {
            boolean[] d = encrypt(e, true, 0, 0, 0);
            out.println("DECRYPTION");
            out.println("Ciphertext C: " + returnBoolArray(e));
            out.println("Key K: " + returnBoolArray(daKey));
            out.println("Plaintext P: " + returnBoolArray(d));
            
        } catch (IOException e) {
            //exception handling left as an exercise for the reader
        }

    }

    // compares the difference between 2 boolean array values for avalanche analysis
    private static int compareDiff(boolean[] arr1, boolean[] arr2) {
        int count = 0;
        for(int i=0; i<arr1.length; i++) {
            if(arr1[i] != arr2[i]) {
                count++;
            }
        }
        return count;
    }

    // reads the text files and converts them to boolean arrays
    private static boolean[] readFile(int lineNumber) {
        boolean[] boolArray = new boolean[64];
        try {
            String data = Files.readAllLines(Paths.get("input.txt")).get(lineNumber);
            StringBuilder sb = new StringBuilder();
            char[] charArray = new char[64];
            sb.append(data);
            charArray = data.toCharArray();
            // convert charArray values into a boolean array
            for(int i=0; i<charArray.length; i++) {
                boolArray[i] = charArray[i] == '1';
            }
        
        } catch (IOException e) {
            System.out.println("An error occurred.");
            e.printStackTrace();
        }
        return boolArray;
    }

    // returns a string of 1s and 0s from boolean array
    private static String returnBoolArray(boolean[] inputArray) {
        String out = "";
        for(int i=0; i<inputArray.length; i++) {
            if(inputArray[i]) {
                out += "1";
            } else {
                out += "0";
            }
        }
        return out;
    }

    // prints a string of 1s and 0s from boolean array
    private static void printBoolArray(boolean[] inputArray) {
        for(int i=0; i<inputArray.length; i++) {
            if(inputArray[i]) {
                System.out.print("1");
            } else {
                System.out.print("0");
            }
        }
        System.out.println();
    }

    // generates 16 subkeys from provided key
    private static void keyGen(boolean[] inputArray, int key) {
        // permuted choice
        inputArray = permutation(inputArray, PC1);
        // split array
        boolean [] c = new boolean[inputArray.length/2];
        boolean [] d = new boolean[inputArray.length/2];
        splitArray(inputArray, c, d);

        // generate 16 keys
        for(int i=0; i < 16; i++) {
            // left shift
            leftShift(c, leftShiftArray[i]);
            leftShift(d, leftShiftArray[i]);
            // join arrays
            boolean[] joinedArray = joinArrays(c, d);
            // permutated choice 2
            boolean[] pArray = permutation(joinedArray, PC2);
            // save array into key array
            for(int j=0; j<pArray.length; j++) {
                keys[key][i][j] = pArray[j];
            }
        }   
    }

    // performs permutation based on permutiation table provided
    private static boolean[] permutation(boolean[] inputArray, int[] permTable) {
        boolean[] outputArray = new boolean[permTable.length];
        for(int i=0; i< permTable.length; i++) {
            setBool(outputArray, i, getBool(inputArray, permTable[i]-1));
        }
        return outputArray;
    }

    // returns boolean
    private static boolean getBool(boolean[] inputArray, int pos) {
        return inputArray[pos];
    }

    // sets boolean
    private static void setBool(boolean[] inputArray, int pos, boolean value) {
        inputArray[pos] = value;
    }

    // perform a left shift on boolean array
    private static boolean[] leftShift(boolean[] input, int shift) {   
        for(int i=0; i < shift; i++) {
            boolean temp = input[0];
            for(int j=1; j<input.length; j++) {
                input[j-1] = input[j];
            }
            input[input.length - 1] = temp;
        }
        return input;
    }

    // splits array in half
    private static void splitArray(boolean[] in, boolean[] out1, boolean[] out2) {
        int middle = in.length/2;
        for (int i = 0; i < middle; i++) {
            out1[i] = in[i];
        }
        for (int i = middle; i < in.length; i++) {
            out2[i - middle] = in[i];
        }
    }

    // joins 2 arrays together
    private static boolean[] joinArrays(boolean[] array1, boolean[] array2) {
        boolean[] newArray = new boolean[array1.length + array2.length];
        int val = 0;
        for (int i = 0; i < array1.length; i++) {
            newArray[val] = array1[i];
            val++;
        }
        for (int i = 0; i < array2.length; i++) {
            newArray[val] = array2[i];
            val++;
        }
        return newArray;
    }

    // prints out keys
    private static void printKeys(int key) {
        System.out.println("Printing keys ================================");
        for(int i=0; i<keys[key].length; i++) {
            printBoolArray(keys[key][i]);
            System.out.println();
        }
    }

    // encryption/decryption function
    private static boolean[] encrypt(boolean[] input, boolean isDecrypt, int desType, 
        int testNumber, int key) {
        boolean[] arr1 = input;
        // initial permutation
        arr1 = permutation(arr1, IP);
        //split
        boolean[] left = new boolean[32];
        boolean[] right = new boolean[32];
        splitArray(arr1, left, right);
        
        // 16 rounds of encryption/decryption
        for(int i=0; i<16; i++) {
            boolean[] tempRight = right;
            // f-function
            if(isDecrypt) {
                right = feistel(right, 15-i, desType, key);
            } else {
                right = feistel(right, i, desType, key);
            }
            // xor
            right = xor(left, right);
            left = tempRight;
            if(!isDecrypt) {
                results[testNumber][desType][i] = joinArrays(left, right);
            }
        }
        // join
        boolean[] arr2 = joinArrays(right, left);
        // inverse permutation
        arr2 = permutation(arr2, invIP);
        return arr2;
    }

    // f-function
    private static boolean[] feistel(boolean[] input, int round, int desType, int key) {
        boolean[] arr1 = input;
        //expansion
        arr1 = permutation(arr1, expandTbl);
        // key mix xor
        if(desType != 1) {
            arr1 = xor(arr1, keys[key][round]);
        }
        // s-box
        if(desType == 2) {
            arr1 = inverseP(arr1);
        } else {
            arr1 = sbox(arr1);
        }
        //permutation
        if(desType != 3) {
            arr1 = permutation(arr1, P);
        }
        return arr1;
    }

    // inverse permutation for DES2
    private static boolean[] inverseP(boolean[] input) {
        boolean[] output = new boolean[32];
        int val = 0;
        int current = 0;
        for(int i=0; i<input.length; i++) {
            if(invExpand[val] == i) {
                val++;
            } else {
                output[current] = input[i];
                current++;
            }
        }
        return output;
    }

    // performs xor on 2 boolean arrays
    private static boolean[] xor(boolean[] input1, boolean[] input2) {
        boolean[] arr1 = new boolean[input1.length];
        for(int i=0; i< input1.length; i++) {
            arr1[i] = input1[i] ^ input2[i]; 
        }
        return arr1;
    }

    // performs sbox function
    private static boolean[] sbox(boolean[] oldArray) {
        boolean[] newArray = new boolean[32];
        boolean[] tempArray = new boolean[6];
        int val = 0;
        int val2 = 0;
        for(int i=0; i<8; i++) {
            for(int j=val; j<val+6; j++) {
                tempArray[j-val] = oldArray[j];
            }
            // set tempArray 0 and 5 to boolRow
            boolean[] boolRow = {tempArray[0], tempArray[5]};
            // set tempArray 1 => 4 to boolCol
            boolean[] boolCol = {tempArray[1], tempArray[2], tempArray[3], tempArray[4]};
            // convert boolRow to decimal
            int decRow = Integer.parseInt(boolArrayToString(boolRow), 2);
            // convert boolCol to decimal
            int decCol = Integer.parseInt(boolArrayToString(boolCol), 2);
            // select correct value in s-box
            int sboxVal = sboxes[i][decRow][decCol];
            // convert selected value to boolean array
            String binString = Integer.toBinaryString(sboxVal);
            binString = String.format("%04d", Integer.parseInt(binString));
            char[] charArray = binString.toCharArray();
            // store values into newArray
            for(int j=0;j<4; j++) {
                newArray[val2] = charArray[j] == '1';
                val2++;
            }
            val += 6;
        }
        return newArray;
    }

    // converts boolean array to string
    private static String boolArrayToString(boolean[] input) {
        StringBuilder binaryString = new StringBuilder();
        for(boolean b : input) {
            if (b) {
                binaryString.append("1");
            } else {
                binaryString.append(0);
            }
        }
        return binaryString.toString();
    }
}
