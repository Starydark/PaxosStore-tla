#### PaxosStoreWithMessageType

最初始的版本，保留消息类型("Prepare"，"Accept"，"ACK")。

#### OneVotePaxosStore

删除消息类型，使用OneVote和IntersectingQuorum来替代Blas(p),即Client-restriced。(Error)

#### OneValuePerBallotPaxosStore

试图解决上述版本error。(Fail)

#### UniversalPaxosStore

大致上和现在的版本一样，Accept动作少了几个限制条件。

#### 