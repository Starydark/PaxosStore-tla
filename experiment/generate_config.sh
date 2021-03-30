#!/bin/bash


three_acc="[model value]<symmetrical>{p1, p2, p3}"
three_quorum="{{p1, p2}, {p1, p3}, {p2, p3}}"

two_acc="[model value]<symmetrical>{p1, p2, p3, p4, p5}"
two_quorum="{{p1, p2, p3}, {p1, p2, p4}, {p1, p2, p5}, {p1, p3, p4}, {p1, p3, p5}, {p1, p4, p5}, {p2, p3, p4}, {p2, p3, p5}, {p2, p4, p5}, {p3, p4, p5}}"

two_val="[model value]{v1, v2}"
three_val="[model value]{v1, v2, v3, v4}"

two_bal="1..4"
three_bal="1..3"

function generate_config() {
    file="$1"
    target="$2"
    name="$3"
    formula="$4"
    invariant="$5"
    prop="$6"
    acc_num=$7
    val_num=$8
    bal_num=$9

    echo "$file $target $name $formula $invariant $prop $acc_num $val_num $bal_num"

    echo "$prop"

    echo "[options]" > $file
    echo "target: $target" >> $file
    echo "model name: $name" >> $file
    echo "workder num: 10" >> $file
    echo "" >> $file

    echo "[behavior]" >> $file
    echo "temporal formula: $formula" >> $file
    echo "" >> $file


    if [[ ! -z "$invariant" ]]; then
        echo "[invariant]" >> $file
        echo "Consistency: $invariant" >> $file
    fi

    if [[ ! -z "$prop" ]]; then
        echo "[properties]" >> $file
        echo "XSpec: $prop" >> $file
    fi
    echo "" >> $file


    echo "[constants]" >> $file 
    if [[ $acc_num -eq 3 ]]; then
        echo "Acceptor: $three_acc" >> $file
        echo "Quorum: $three_quorum" >> $file
    else 
        echo "Acceptor: $two_acc" >> $file
        echo "Quorum: $two_quorum" >> $file
    fi


    if [[ $val_num -eq 3 ]]; then
        echo "Value: $three_val" >> $file
    else
        echo "Value: $two_val" >> $file
    fi
    echo "" >> $file

    echo "[override]" >> $file
    echo "None: [model value]" >> $file

    if [[ 3 -eq "$bal_num" ]]; then
        echo "Nat: $two_bal" >> $file
    else
        echo "Nat: $three_bal" >> $file
    fi
}

function Main() {

    pwd

    config_path="./Eager_config"

    if [[ ! -d "$config_path" ]];then
        echo "$config_path is not a dir"
        exit 1
    fi

    cd $config_path
    
    file="$1"
    target="$2"
    name="$3"
    formula="$4"
    invariant="$5"
    prop="$6"
    acc_num=$7
    val_num=$8
    bal_num=$9

    for acceptor in `seq 2 3`; do
        for value in `seq 2 3`; do
            for ballot in `seq 2 3`; do
                # file_name="VotingRefEagerV_p${acceptor}_v${value}_n${ballot}.ini"
                # target="TPaxos/Voting.tla"
                # model_name="VotingRefEagerV/p${acceptor}_v${value}_n${ballot}"
                # formula="Spec"
                # invariant=""
                # prop="V!Spec"

                file_name="EagerVRefCons_p${acceptor}_v${value}_n${ballot}.ini"
                target="TPaxos/EagerVoting.tla"
                model_name="EagerVRefCons/p${acceptor}_v${value}_n${ballot}"
                formula="Spec"
                invariant=""
                prop="C!Spec"

                # file_name="EagerVRefVoting_p${acceptor}_v${value}_n${ballot}.ini"
                # target="TPaxos/EagerVotingStuttering.tla"
                # model_name="EagerVRefVoting/p${acceptor}_v${value}_n${ballot}"
                # formula="SpecS"
                # invariant=""
                # prop="V!Spec"

                # echo "$file_name $model_name"

                generate_config $file_name $target $model_name $formula "$invariant" "$prop" $acceptor $value $ballot

            done
        done
    done
}

Main