ENTRY(_start)

PHDRS
{
    text PT_LOAD FLAGS(5);   /* Read + Execute */
    data PT_LOAD FLAGS(6);   /* Read + Write */
}

SECTIONS
{
    . = 0;

    .text : ALIGN(4)
    {
        *(.text.start)
        *(.text)
        *(.text.*)
    } :text

    .rodata : ALIGN(4)
    {
        *(.rodata)
        *(.rodata.*)
        *(.srodata)
        *(.srodata.*)
    } :text

    .data : ALIGN(4)
    {
        *(.data)
        *(.data.*)

        . = ALIGN(4);
        PROVIDE(__global_pointer$ = . + 0x800);

        *(.sdata)
        *(.sdata.*)
    } :data

    .bss (NOLOAD) : ALIGN(4)
    {
        *(.sbss)
        *(.sbss.*)
        *(.bss)
        *(.bss.*)
        *(COMMON)
    } :data
}
