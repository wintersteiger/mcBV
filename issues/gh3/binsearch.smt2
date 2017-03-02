
(set-option :produce-models true)

(declare-fun |goto_symex::&92;guard#1| () Bool)

(declare-fun |goto_symex::&92;guard#2| () Bool)

(declare-fun |goto_symex::&92;guard#3| () Bool)

(declare-fun |goto_symex::&92;guard#4| () Bool)

(declare-fun |goto_symex::&92;guard#5| () Bool)

(declare-fun |goto_symex::&92;guard#6| () Bool)

(declare-fun |goto_symex::&92;guard#7| () Bool)

(declare-fun |goto_symex::&92;guard#8| () Bool)

(declare-fun |goto_symex::&92;guard#9| () Bool)

(declare-fun |goto_symex::&92;guard#10| () Bool)

(declare-fun |goto_symex::&92;guard#11| () Bool)

(declare-fun |goto_symex::&92;guard#12| () Bool)

(declare-fun |goto_symex::&92;guard#13| () Bool)

(declare-fun |goto_symex::&92;guard#14| () Bool)

(declare-fun |goto_symex::&92;guard#15| () Bool)

(declare-fun |goto_symex::&92;guard#16| () Bool)

(declare-fun |BITS#1| () (_ BitVec 32))
(assert (= |BITS#1| (_ bv16 32)))


(declare-fun |__CPROVER_dead_object#1| () (_ BitVec 64))
(assert (= |__CPROVER_dead_object#1| (_ bv0 64)))


(declare-fun |__CPROVER_deallocated#1| () (_ BitVec 64))
(assert (= |__CPROVER_deallocated#1| (_ bv0 64)))


(declare-fun |__CPROVER_malloc_is_new_array#1| () Bool)
(assert (= |__CPROVER_malloc_is_new_array#1| false))


(declare-fun |__CPROVER_malloc_object#1| () (_ BitVec 64))
(assert (= |__CPROVER_malloc_object#1| (_ bv0 64)))


(declare-fun |__CPROVER_malloc_size#1| () (_ BitVec 64))
(assert (= |__CPROVER_malloc_size#1| (_ bv0 64)))


(declare-fun |__CPROVER_memory_leak#1| () (_ BitVec 64))
(assert (= |__CPROVER_memory_leak#1| (_ bv0 64)))


(declare-fun |__CPROVER_next_thread_id#1| () (_ BitVec 64))
(assert (= |__CPROVER_next_thread_id#1| (_ bv0 64)))


(declare-fun |__CPROVER_pipe_count#1| () (_ BitVec 32))
(assert (= |__CPROVER_pipe_count#1| (_ bv0 32)))


(declare-fun |__CPROVER_rounding_mode!0#1| () (_ BitVec 32))
(assert (= |__CPROVER_rounding_mode!0#1| (_ bv0 32)))


(declare-fun |__CPROVER_thread_id!0#1| () (_ BitVec 64))
(assert (= |__CPROVER_thread_id!0#1| (_ bv0 64)))


(declare-fun array_of.0 () (Array (_ BitVec 64) (_ BitVec 1)))
(declare-fun |__CPROVER_threads_exited#1| () (Array (_ BitVec 64) (_ BitVec 1)))
(assert (= |__CPROVER_threads_exited#1| array_of.0))


(declare-fun |main::1::freevar!0@1#2| () (_ BitVec 32))
(assert (= |main::1::freevar!0@1#2| (_ bv6 32)))


(declare-fun |nondet_symex::nondet0| () (_ BitVec 32))
(declare-fun |main::$tmp::return_value_nondet_uint$1!0@1#2| () (_ BitVec 32))
(assert (= |main::$tmp::return_value_nondet_uint$1!0@1#2| |nondet_symex::nondet0|))


(declare-fun |main::1::I!0@1#2| () (_ BitVec 32))
(assert (= |main::1::I!0@1#2| |main::$tmp::return_value_nondet_uint$1!0@1#2|))


(declare-fun |main::1::O!0@1#2| () (_ BitVec 32))
(assert (= |main::1::O!0@1#2| (_ bv0 32)))


(declare-fun |main::1::i!0@1#2| () (_ BitVec 32))
(assert (= |main::1::i!0@1#2| (_ bv0 32)))


(declare-fun |main::1::m!0@1#2| () (_ BitVec 32))
(assert (= |main::1::m!0@1#2| (_ bv2147483648 32)))


(assert (= |goto_symex::&92;guard#1| (bvuge |main::1::I!0@1#2| (_ bv2147483648 32))))

(declare-fun |main::1::O!0@1#3| () (_ BitVec 32))
(assert (= |main::1::O!0@1#3| (_ bv2147483648 32)))


(declare-fun |main::1::O!0@1#4| () (_ BitVec 32))
(assert (= |main::1::O!0@1#4| (ite |goto_symex::&92;guard#1| (_ bv2147483648 32) (_ bv0 32))))


(declare-fun |main::1::i!0@1#3| () (_ BitVec 32))
(assert (= |main::1::i!0@1#3| (_ bv1 32)))


(declare-fun |main::1::m!0@1#3| () (_ BitVec 32))
(assert (= |main::1::m!0@1#3| (_ bv1073741824 32)))


(assert (= |goto_symex::&92;guard#2| (bvuge |main::1::I!0@1#2| (bvadd (_ bv1073741824 32) |main::1::O!0@1#4|))))

(declare-fun |main::1::O!0@1#5| () (_ BitVec 32))
(assert (= |main::1::O!0@1#5| (bvadd (_ bv1073741824 32) |main::1::O!0@1#4|)))


(declare-fun |main::1::O!0@1#6| () (_ BitVec 32))
(assert (= |main::1::O!0@1#6| (ite |goto_symex::&92;guard#2| |main::1::O!0@1#5| |main::1::O!0@1#4|)))


(declare-fun |main::1::i!0@1#4| () (_ BitVec 32))
(assert (= |main::1::i!0@1#4| (_ bv2 32)))


(declare-fun |main::1::m!0@1#4| () (_ BitVec 32))
(assert (= |main::1::m!0@1#4| (_ bv536870912 32)))


(assert (= |goto_symex::&92;guard#3| (bvuge |main::1::I!0@1#2| (bvadd (_ bv536870912 32) |main::1::O!0@1#6|))))

(declare-fun |main::1::O!0@1#7| () (_ BitVec 32))
(assert (= |main::1::O!0@1#7| (bvadd (_ bv536870912 32) |main::1::O!0@1#6|)))


(declare-fun |main::1::O!0@1#8| () (_ BitVec 32))
(assert (= |main::1::O!0@1#8| (ite |goto_symex::&92;guard#3| |main::1::O!0@1#7| |main::1::O!0@1#6|)))


(declare-fun |main::1::i!0@1#5| () (_ BitVec 32))
(assert (= |main::1::i!0@1#5| (_ bv3 32)))


(declare-fun |main::1::m!0@1#5| () (_ BitVec 32))
(assert (= |main::1::m!0@1#5| (_ bv268435456 32)))


(assert (= |goto_symex::&92;guard#4| (bvuge |main::1::I!0@1#2| (bvadd (_ bv268435456 32) |main::1::O!0@1#8|))))

(declare-fun |main::1::O!0@1#9| () (_ BitVec 32))
(assert (= |main::1::O!0@1#9| (bvadd (_ bv268435456 32) |main::1::O!0@1#8|)))


(declare-fun |main::1::O!0@1#10| () (_ BitVec 32))
(assert (= |main::1::O!0@1#10| (ite |goto_symex::&92;guard#4| |main::1::O!0@1#9| |main::1::O!0@1#8|)))


(declare-fun |main::1::i!0@1#6| () (_ BitVec 32))
(assert (= |main::1::i!0@1#6| (_ bv4 32)))


(declare-fun |main::1::m!0@1#6| () (_ BitVec 32))
(assert (= |main::1::m!0@1#6| (_ bv134217728 32)))


(assert (= |goto_symex::&92;guard#5| (bvuge |main::1::I!0@1#2| (bvadd (_ bv134217728 32) |main::1::O!0@1#10|))))

(declare-fun |main::1::O!0@1#11| () (_ BitVec 32))
(assert (= |main::1::O!0@1#11| (bvadd (_ bv134217728 32) |main::1::O!0@1#10|)))


(declare-fun |main::1::O!0@1#12| () (_ BitVec 32))
(assert (= |main::1::O!0@1#12| (ite |goto_symex::&92;guard#5| |main::1::O!0@1#11| |main::1::O!0@1#10|)))


(declare-fun |main::1::i!0@1#7| () (_ BitVec 32))
(assert (= |main::1::i!0@1#7| (_ bv5 32)))


(declare-fun |main::1::m!0@1#7| () (_ BitVec 32))
(assert (= |main::1::m!0@1#7| (_ bv67108864 32)))


(assert (= |goto_symex::&92;guard#6| (bvuge |main::1::I!0@1#2| (bvadd (_ bv67108864 32) |main::1::O!0@1#12|))))

(declare-fun |main::1::O!0@1#13| () (_ BitVec 32))
(assert (= |main::1::O!0@1#13| (bvadd (_ bv67108864 32) |main::1::O!0@1#12|)))


(declare-fun |main::1::O!0@1#14| () (_ BitVec 32))
(assert (= |main::1::O!0@1#14| (ite |goto_symex::&92;guard#6| |main::1::O!0@1#13| |main::1::O!0@1#12|)))


(declare-fun |main::1::i!0@1#8| () (_ BitVec 32))
(assert (= |main::1::i!0@1#8| (_ bv6 32)))


(declare-fun |main::1::m!0@1#8| () (_ BitVec 32))
(assert (= |main::1::m!0@1#8| (_ bv33554432 32)))


(assert (= |goto_symex::&92;guard#7| (bvuge |main::1::I!0@1#2| (bvadd (_ bv33554432 32) |main::1::O!0@1#14|))))

(declare-fun |main::1::O!0@1#15| () (_ BitVec 32))
(assert (= |main::1::O!0@1#15| (bvadd (_ bv33554432 32) |main::1::O!0@1#14|)))


(declare-fun |main::1::O!0@1#16| () (_ BitVec 32))
(assert (= |main::1::O!0@1#16| (ite |goto_symex::&92;guard#7| |main::1::O!0@1#15| |main::1::O!0@1#14|)))


(declare-fun |main::1::i!0@1#9| () (_ BitVec 32))
(assert (= |main::1::i!0@1#9| (_ bv7 32)))


(declare-fun |main::1::m!0@1#9| () (_ BitVec 32))
(assert (= |main::1::m!0@1#9| (_ bv16777216 32)))


(assert (= |goto_symex::&92;guard#8| (bvuge |main::1::I!0@1#2| (bvadd (_ bv16777216 32) |main::1::O!0@1#16|))))

(declare-fun |main::1::O!0@1#17| () (_ BitVec 32))
(assert (= |main::1::O!0@1#17| (bvadd (_ bv16777216 32) |main::1::O!0@1#16|)))


(declare-fun |main::1::O!0@1#18| () (_ BitVec 32))
(assert (= |main::1::O!0@1#18| (ite |goto_symex::&92;guard#8| |main::1::O!0@1#17| |main::1::O!0@1#16|)))


(declare-fun |main::1::i!0@1#10| () (_ BitVec 32))
(assert (= |main::1::i!0@1#10| (_ bv8 32)))


(declare-fun |main::1::m!0@1#10| () (_ BitVec 32))
(assert (= |main::1::m!0@1#10| (_ bv8388608 32)))


(assert (= |goto_symex::&92;guard#9| (bvuge |main::1::I!0@1#2| (bvadd (_ bv8388608 32) |main::1::O!0@1#18|))))

(declare-fun |main::1::O!0@1#19| () (_ BitVec 32))
(assert (= |main::1::O!0@1#19| (bvadd (_ bv8388608 32) |main::1::O!0@1#18|)))


(declare-fun |main::1::O!0@1#20| () (_ BitVec 32))
(assert (= |main::1::O!0@1#20| (ite |goto_symex::&92;guard#9| |main::1::O!0@1#19| |main::1::O!0@1#18|)))


(declare-fun |main::1::i!0@1#11| () (_ BitVec 32))
(assert (= |main::1::i!0@1#11| (_ bv9 32)))


(declare-fun |main::1::m!0@1#11| () (_ BitVec 32))
(assert (= |main::1::m!0@1#11| (_ bv4194304 32)))


(assert (= |goto_symex::&92;guard#10| (bvuge |main::1::I!0@1#2| (bvadd (_ bv4194304 32) |main::1::O!0@1#20|))))

(declare-fun |main::1::O!0@1#21| () (_ BitVec 32))
(assert (= |main::1::O!0@1#21| (bvadd (_ bv4194304 32) |main::1::O!0@1#20|)))


(declare-fun |main::1::O!0@1#22| () (_ BitVec 32))
(assert (= |main::1::O!0@1#22| (ite |goto_symex::&92;guard#10| |main::1::O!0@1#21| |main::1::O!0@1#20|)))


(declare-fun |main::1::i!0@1#12| () (_ BitVec 32))
(assert (= |main::1::i!0@1#12| (_ bv10 32)))


(declare-fun |main::1::m!0@1#12| () (_ BitVec 32))
(assert (= |main::1::m!0@1#12| (_ bv2097152 32)))


(assert (= |goto_symex::&92;guard#11| (bvuge |main::1::I!0@1#2| (bvadd (_ bv2097152 32) |main::1::O!0@1#22|))))

(declare-fun |main::1::O!0@1#23| () (_ BitVec 32))
(assert (= |main::1::O!0@1#23| (bvadd (_ bv2097152 32) |main::1::O!0@1#22|)))


(declare-fun |main::1::O!0@1#24| () (_ BitVec 32))
(assert (= |main::1::O!0@1#24| (ite |goto_symex::&92;guard#11| |main::1::O!0@1#23| |main::1::O!0@1#22|)))


(declare-fun |main::1::i!0@1#13| () (_ BitVec 32))
(assert (= |main::1::i!0@1#13| (_ bv11 32)))


(declare-fun |main::1::m!0@1#13| () (_ BitVec 32))
(assert (= |main::1::m!0@1#13| (_ bv1048576 32)))


(assert (= |goto_symex::&92;guard#12| (bvuge |main::1::I!0@1#2| (bvadd (_ bv1048576 32) |main::1::O!0@1#24|))))

(declare-fun |main::1::O!0@1#25| () (_ BitVec 32))
(assert (= |main::1::O!0@1#25| (bvadd (_ bv1048576 32) |main::1::O!0@1#24|)))


(declare-fun |main::1::O!0@1#26| () (_ BitVec 32))
(assert (= |main::1::O!0@1#26| (ite |goto_symex::&92;guard#12| |main::1::O!0@1#25| |main::1::O!0@1#24|)))


(declare-fun |main::1::i!0@1#14| () (_ BitVec 32))
(assert (= |main::1::i!0@1#14| (_ bv12 32)))


(declare-fun |main::1::m!0@1#14| () (_ BitVec 32))
(assert (= |main::1::m!0@1#14| (_ bv524288 32)))


(assert (= |goto_symex::&92;guard#13| (bvuge |main::1::I!0@1#2| (bvadd (_ bv524288 32) |main::1::O!0@1#26|))))

(declare-fun |main::1::O!0@1#27| () (_ BitVec 32))
(assert (= |main::1::O!0@1#27| (bvadd (_ bv524288 32) |main::1::O!0@1#26|)))


(declare-fun |main::1::O!0@1#28| () (_ BitVec 32))
(assert (= |main::1::O!0@1#28| (ite |goto_symex::&92;guard#13| |main::1::O!0@1#27| |main::1::O!0@1#26|)))


(declare-fun |main::1::i!0@1#15| () (_ BitVec 32))
(assert (= |main::1::i!0@1#15| (_ bv13 32)))


(declare-fun |main::1::m!0@1#15| () (_ BitVec 32))
(assert (= |main::1::m!0@1#15| (_ bv262144 32)))


(assert (= |goto_symex::&92;guard#14| (bvuge |main::1::I!0@1#2| (bvadd (_ bv262144 32) |main::1::O!0@1#28|))))

(declare-fun |main::1::O!0@1#29| () (_ BitVec 32))
(assert (= |main::1::O!0@1#29| (bvadd (_ bv262144 32) |main::1::O!0@1#28|)))


(declare-fun |main::1::O!0@1#30| () (_ BitVec 32))
(assert (= |main::1::O!0@1#30| (ite |goto_symex::&92;guard#14| |main::1::O!0@1#29| |main::1::O!0@1#28|)))


(declare-fun |main::1::i!0@1#16| () (_ BitVec 32))
(assert (= |main::1::i!0@1#16| (_ bv14 32)))


(declare-fun |main::1::m!0@1#16| () (_ BitVec 32))
(assert (= |main::1::m!0@1#16| (_ bv131072 32)))


(assert (= |goto_symex::&92;guard#15| (bvuge |main::1::I!0@1#2| (bvadd (_ bv131072 32) |main::1::O!0@1#30|))))

(declare-fun |main::1::O!0@1#31| () (_ BitVec 32))
(assert (= |main::1::O!0@1#31| (bvadd (_ bv131072 32) |main::1::O!0@1#30|)))


(declare-fun |main::1::O!0@1#32| () (_ BitVec 32))
(assert (= |main::1::O!0@1#32| (ite |goto_symex::&92;guard#15| |main::1::O!0@1#31| |main::1::O!0@1#30|)))


(declare-fun |main::1::i!0@1#17| () (_ BitVec 32))
(assert (= |main::1::i!0@1#17| (_ bv15 32)))


(declare-fun |main::1::m!0@1#17| () (_ BitVec 32))
(assert (= |main::1::m!0@1#17| (_ bv65536 32)))


(assert (= |goto_symex::&92;guard#16| (bvuge |main::1::I!0@1#2| (bvadd (_ bv65536 32) |main::1::O!0@1#32|))))

(declare-fun |main::1::O!0@1#33| () (_ BitVec 32))
(assert (= |main::1::O!0@1#33| (bvadd (_ bv65536 32) |main::1::O!0@1#32|)))


(declare-fun |main::1::O!0@1#34| () (_ BitVec 32))
(assert (= |main::1::O!0@1#34| (ite |goto_symex::&92;guard#16| |main::1::O!0@1#33| |main::1::O!0@1#32|)))


(declare-fun |main::1::i!0@1#18| () (_ BitVec 32))
(assert (= |main::1::i!0@1#18| (_ bv16 32)))


(declare-fun |main::1::freevar!0@1#1| () (_ BitVec 32))

(declare-fun |main::1::I!0@1#1| () (_ BitVec 32))

(declare-fun |main::$tmp::return_value_nondet_uint$1!0@1#1| () (_ BitVec 32))

(declare-fun |main::1::O!0@1#1| () (_ BitVec 32))

(declare-fun |main::1::m!0@1#1| () (_ BitVec 32))

(declare-fun |main::1::i!0@1#1| () (_ BitVec 32))

(check-sat)

