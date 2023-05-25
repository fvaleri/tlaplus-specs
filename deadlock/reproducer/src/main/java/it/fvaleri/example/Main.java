package it.fvaleri.example;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Deadlock reproducer.
 */
public class Main {
    private static final Random RND = new Random(0);

    // Constants.
    private static final int BUFFER_CAPACITY = 5;
    private static final int NUM_OF_PRODUCERS = 10;
    private static final int NUM_OF_CONSUMERS = 3;
    private static final int CHECK_INTERVAL_MS = 60_000;
    private static final int PRODUCER_MAX_SLEEP_MS = 10;
    private static final int CONSUMER_MAX_SLEEP_MS = 3;

    // Variables.
    private static BlockingQueue<String> queue = new BlockingQueue<>(BUFFER_CAPACITY);
    private static List<Thread> participants = new ArrayList<>();

    public static void main(String[] args) {
        try {
            for (int i = 0; i < NUM_OF_PRODUCERS; i++) {
                Producer t = new Producer(i);
                participants.add(t);
                t.start();
            }
            for (int i = 0; i < NUM_OF_CONSUMERS; i++) {
                Consumer t = new Consumer(i);
                participants.add(t);
                t.start();
            }
            int threadCount = participants.size();

            long start = System.nanoTime();
            while (true) {
                Thread.sleep(CHECK_INTERVAL_MS);
                synchronized(queue) {
                    if (queue.waitSetSize() == threadCount) {
                        System.err.printf("DEADLOCK after %d messages and %.1f seconds!",
                                queue.msgCount(), (queue.lastChange() - start) / 1e9);
                        for (Thread t : participants) {
                            t.interrupt();
                        }
                        return;
                    }
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    static class Producer extends Thread {
        public Producer(int n) {
            super("producer-" + n);
        }

        public void run() {
            String name = getName();
            try {
                while (true) {
                    sleep(RND.nextInt(PRODUCER_MAX_SLEEP_MS)); // Simulates non deterministic processing
                    queue.put(name);
                }
            } catch (InterruptedException e) {
            }
        }
    }

    static class Consumer extends Thread {
        public Consumer(int n) {
            super("consumer-" + n);
        }

        public void run() {
            String name = getName();
            try {
                while (true) {
                    queue.get();
                    sleep(RND.nextInt(CONSUMER_MAX_SLEEP_MS)); // Simulates non deterministic processing
                }
            } catch (InterruptedException e) {
            }
        }
    }
}
