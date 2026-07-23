Require Export ASN1Parser.ExtrOCaml.Extract.
(*Require Import NR.BCCH_DL_SCH_Message.
Require Import NR.DL_CCCH_Message.
Require Import NR.PCCH_Message.
Require Import NR.MCCH_Message_r17.

Require Import NR.UL_CCCH_Message.
Require Import NR.UL_DCCH_Message. *)

Require Import NR.DL_DCCH_Message.

Set Extraction KeepSingleton.

Extraction "../../ExtrTest_NR/src/FormatTest.ml"  DL_DCCH_Message__Format. (*BCCH_DL_SCH_Message__Format DL_CCCH_Message__Format PCCH_Message__Format MCCH_Message_r17__Format DL_DCCH_Message__Format UL_CCCH_Message__Format UL_DCCH_Message__Format. *)


