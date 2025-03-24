# Operating System

## 📌 Introduction

This project was carried out using the **xv6 educational operating system** to gain a deeper understanding of key concepts in **Operating Systems**. The following three features were implemented independently within xv6 to explore core topics such as CPU scheduling, threading, and memory management.

- 🧠 **(Project 02) Custom CPU Scheduling**  
  The default **Round Robin** scheduling algorithm in xv6 was modified to support multiple custom scheduling policies. This allowed exploration of how different strategies affect process execution and fairness in the kernel.

[CPU_Scheduling_report](./OS_project02_11741_2022006135/OS_project02_11741_2022006135.pdf)

- 🧵 **(Project 03) Thread Implementation**  
  A lightweight threading mechanism was introduced to allow multiple threads to run concurrently within a process. This involved modifying xv6's process control structures and system calls to manage thread creation, execution, and termination.

[Thread_Implementation_report](./OS_project03_11741_2022006135/OS_project03_11741_2022006135.pdf)

- 📦 **(Project 04) Copy-on-Write (COW)**  
  To reduce memory overhead during process creation, a **Copy-on-Write** mechanism was implemented. Instead of immediately allocating new physical pages for child processes, they initially share the parent's pages and only copy them upon write attempts.

[Copy_on_Write_Implementation_report](./OS_project04_11741_2022006135/OS_project04_11741_2022006135_문준영.pdf)

Each component was developed and tested **independently**, without interference from the others, to ensure modular understanding and correctness of each system-level feature.
