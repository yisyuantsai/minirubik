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
        *(.text)
        *(.text.*)
    } :text

    .rodata : ALIGN(2)
    {
        *(.rodata)
        *(.rodata.*)
    } :text

    .data : ALIGN(4)
    {
        *(.data)
        *(.data.*)
        *(.sdata)
        *(.sdata.*)
    } :data

    .bss (NOLOAD) : ALIGN(4)
    {
        *(.bss)
        *(.bss.*)
        *(COMMON)
    } :data
}