#lang forge 


sig Message {}

sig State {
    messages: set Message
}

// 初始状态：包含一个消息
pred initState[s: State, m: Message] {
    s.messages = {m}
}

// 操作：向集合中添加一个消息
pred addMessage[s: State, s': State, m: Message] {
    s'.messages = s.messages + m
    // 确保新消息之前不在集合中
    m not in s.messages
}

// 检验模型：从初始状态开始，然后添加一些消息
run {
    some m: Message, s, s': State |
    initState[s, m] and addMessage[s, s', Message]
} for 5 Message, 3 State
