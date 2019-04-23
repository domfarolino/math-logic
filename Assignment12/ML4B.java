// ML4B.java CS6021 cheng 2019  
// reference: Benjamin's Java 8 Concurrency Tutorial 2015
// A pool of two threads sharing the same memory location "count"
// Each performs read, add, store
// Race condition may occur and some of the increments may get lost.
// Usage: java ML4B 1
// Usage: java ML4B 2
// Usage: java ML4B 3

import java.io.*;
import java.util.*;
import java.util.stream.*;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

public class ML4B{

 public static void stop(ExecutorService executor) {  // common function defined by Benjamin
        try {
            executor.shutdown();
            executor.awaitTermination(60, TimeUnit.SECONDS);
        }
        catch (InterruptedException e) {
            System.err.println("termination interrupted");
        }
        finally {
            if (!executor.isTerminated()) {
                System.err.println("killing non-finished tasks");
            }
            executor.shutdownNow();
        }
    }

int count = 0;  // shared memory

void increment() {  // three steps: read count, add one to value, store at count
    count = count + 1;
}

synchronized void incrementSync() {  // used in race2() as part of a monitor
    count = count + 1;
}

ReentrantLock lock = new ReentrantLock(); 

void incrementWithReentrancelock() {  // Java's ReentrantLock, used in race3()
    lock.lock();
    try {
        count++;
    } finally {
        lock.unlock();
    }
}

void race1(){  // simple race condition

ExecutorService executor = Executors.newFixedThreadPool(2);

IntStream.range(0, 10000)
    .forEach(i -> executor.submit(this::increment));

stop(executor);

System.out.println(count); 
}

void race2(){  // monitor provided in Java

ExecutorService executor = Executors.newFixedThreadPool(2);

IntStream.range(0, 10000)
    .forEach(i -> executor.submit(this::incrementSync));

stop(executor);

System.out.println(count); 
}

void race3(){  // Java's ReentrantLock

ExecutorService executor = Executors.newFixedThreadPool(2);

IntStream.range(0, 10000)
    .forEach(i -> executor.submit(this::incrementWithReentrancelock));

stop(executor);

System.out.println(count); 
}


public static void main(String[] args){
 ML4B ml4 = new ML4B();
 if (args.length < 1) ml4.race1();
 else{
    int c = Integer.parseInt(args[0]);
    switch (c){
      case 1: ml4.race1(); break;
      case 2: ml4.race2(); break;
      case 3: ml4.race3(); break;
      default: ;
    }
 }
}
}