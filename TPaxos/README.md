#### Accept动作分析

根据TPaxos $\Rightarrow$ EagerVoting的refinement mapping：

​					maxBal $\leftarrow$ states[p]p].maxBal

并且TPaxos执行的Accept(p, b, v)动作对应的应该是EagerVoting中的VoteFor(a, b, v)动作：

​	![1567300881880](C:\Users\pure_\AppData\Roaming\Typora\typora-user-images\1567300881880.png)
​	Accept(p, b, v)应该满足VoteFor的动作，先分析第一条，即转换成states[p]p].maxBal $\leq$ b，当p能进行b轮的accept阶段意味着该轮的prepare阶段已经进行过了，即states[p]p].maxBal $\geq$ b，所以states[p]p].maxBal = b。

​	对于第二条而言，我们需要在Accept中限制b轮的Accept动作不能发生第二次，是不是可以添加条件states[p]p].maxVBal # b 即 states[p]p].maxVBal < b（根据上面maxBal分析得出）。

​	添加了这两个条件后，严格限制了Accept动作的执行时间，当且仅当b对应的参与者通过了prepare请求并且它**没有对更高的编号make promise**。Accept阶段相当于Paxos中的P2a+一个P2b，相对于Paxos的p2a阶段由于p2b加了限制。

​	对于原TPaxos算法而言，文字描述的是经过了issue($m_i$)后等到了多数派的认可后可以进行issue($P_i$)，如果这两个动作之间发生了OnMessage并make promise，能不能进行issue($P_i$)?